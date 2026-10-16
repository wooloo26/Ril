//! Managed channel descriptors and certified ticket-graph transport. Host waits
//! and recursive physical channel closure belong outside these heap operations.
use crate::{
    channel::{self, Context, Detached, Endpoint},
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

impl Runtime {
    pub(crate) fn channel_context(&self) -> Context<'_> {
        Context {
            owner: self.task_owner,
            lineage: &self.scope_lineage,
        }
    }
    pub(crate) fn allocate_channel_endpoint(&mut self, endpoint: Endpoint) -> Result<Handle> {
        let object = match &endpoint {
            Endpoint::Sender(value) => Object::ChannelSender(value.clone()),
            Endpoint::Receiver(value) => Object::ChannelReceiver(value.clone()),
        };
        let handle = self.allocate(object)?;
        self.owned_endpoints.push((handle, endpoint));
        Ok(handle)
    }
    pub(crate) fn allocate_channel_ticket(&mut self, ticket: Arc<Detached>) -> Result<Handle> {
        let handle = self.allocate(Object::ChannelDetached(ticket.clone()))?;
        self.owned_tickets.push((handle, ticket));
        Ok(handle)
    }
    pub(crate) fn create_channel(&mut self, capacity: i128) -> Result<Handle> {
        let scope = self
            .scope_registry
            .last()
            .cloned()
            .ok_or_else(|| RuntimeError::panic("channel creation requires an owning scope"))?;
        let (sender, receiver) = channel::bounded(capacity, scope.id(), self.channel_context())?;
        let sender = Endpoint::Sender(sender);
        let sender_handle = self.allocate_channel_endpoint(sender.clone())?;
        scope.register_channel(sender_handle, sender)?;
        let receiver = Endpoint::Receiver(receiver);
        let receiver_handle = self.allocate_channel_endpoint(receiver.clone())?;
        scope.register_channel(receiver_handle, receiver)?;
        self.allocate(Object::Tuple(vec![sender_handle, receiver_handle]))
    }
    pub(crate) fn channel_endpoint(&self, handle: Handle) -> Result<Endpoint> {
        match self.heap.get(handle)? {
            Object::ChannelSender(value) => Ok(Endpoint::Sender(value.clone())),
            Object::ChannelReceiver(value) => Ok(Endpoint::Receiver(value.clone())),
            _ => Err(RuntimeError::internal("expected channel endpoint")),
        }
    }
    pub(crate) fn channel_tickets(&self, root: Handle) -> Result<Vec<(Handle, Arc<Detached>)>> {
        let mut pending = vec![root];
        let mut visited = BTreeSet::new();
        let mut tickets = vec![];
        while let Some(handle) = pending.pop() {
            if !visited.insert(handle) {
                continue;
            }
            let object = self.heap.get(handle)?;
            if let Object::ChannelDetached(ticket) = object {
                tickets.push((handle, ticket.clone()));
            } else {
                pending.extend(object.value_references());
            }
        }
        Ok(tickets)
    }
    pub(crate) fn transfer_captured_tickets(
        &mut self,
        root: Handle,
        target: Context<'_>,
    ) -> Result<Vec<(Handle, Arc<Detached>)>> {
        let tickets = self.channel_tickets(root)?;
        for (_, ticket) in &tickets {
            ticket.validate_owner(self.channel_context())?;
            if !target.lineage.contains(&ticket.scope_id()) {
                return Err(RuntimeError::panic(
                    "captured ticket leaves its owning scope",
                ));
            }
        }
        let mut transferred = BTreeSet::new();
        for (_, ticket) in &tickets {
            if transferred.insert(ticket.identity()) {
                ticket.transfer_owner(self.task_owner, target)?;
            }
        }
        Ok(tickets)
    }
    pub(crate) fn reissue_returned_tickets(
        &mut self,
        root: Handle,
        target: Context<'_>,
    ) -> Result<Handle> {
        let tickets = self.channel_tickets(root)?;
        for (_, ticket) in &tickets {
            ticket.validate_owner(self.channel_context())?;
            if !target.lineage.contains(&ticket.scope_id()) {
                return Err(RuntimeError::panic(
                    "returned ticket leaves its owning scope",
                ));
            }
        }
        let mut issued = BTreeMap::new();
        let mut replacements = BTreeMap::new();
        for (handle, ticket) in tickets {
            let identity = ticket.identity();
            let replacement = if let Some(&value) = issued.get(&identity) {
                value
            } else {
                let fresh = ticket.reissue(self.channel_context(), target)?;
                let value = self.allocate_channel_ticket(fresh)?;
                issued.insert(identity, value);
                value
            };
            replacements.insert(handle, replacement);
        }
        let value = self.heap.replace_ticket_graph(root, &replacements)?;
        self.keep_temporary(value);
        Ok(value)
    }
    pub(crate) fn adopt_received_tickets(&mut self, root: Handle) -> Result<()> {
        let tickets = self.channel_tickets(root)?;
        for (_, ticket) in &tickets {
            ticket.validate_owner(self.channel_context())?;
        }
        for (handle, ticket) in tickets {
            if !self
                .owned_tickets
                .iter()
                .any(|(existing, _)| *existing == handle)
            {
                self.owned_tickets.push((handle, ticket));
            }
        }
        Ok(())
    }
    pub(crate) fn replace_received_tickets(
        &mut self,
        root: Handle,
        tickets: &[(Handle, Arc<Detached>)],
    ) -> Result<Handle> {
        let mut allocated = BTreeMap::new();
        let mut replacements = BTreeMap::new();
        for (handle, ticket) in tickets {
            ticket.validate_owner(self.channel_context())?;
            let identity = ticket.identity();
            let replacement = if let Some(&value) = allocated.get(&identity) {
                value
            } else {
                let value = self.allocate_channel_ticket(ticket.clone())?;
                allocated.insert(identity, value);
                value
            };
            replacements.insert(*handle, replacement);
        }
        let value = self.heap.replace_ticket_graph(root, &replacements)?;
        self.keep_temporary(value);
        Ok(value)
    }
    pub(crate) fn clone_channel_sender(&mut self, handle: Handle) -> Result<Option<Handle>> {
        let Object::ChannelSender(sender) = self.heap.get(handle)? else {
            return Ok(None);
        };
        let clone = sender.clone_for(self.channel_context())?;
        self.allocate_channel_endpoint(Endpoint::Sender(clone))
            .map(Some)
    }
}

#[cfg(test)]
mod tests;
