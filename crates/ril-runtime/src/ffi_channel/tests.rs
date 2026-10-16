use super::*;

fn fixture() {
    ril_rt_init();
    with_runtime(|runtime| {
        let scope = crate::concurrent::Scope::new(&runtime.cancellation).unwrap();
        runtime.scope_lineage.push(scope.id());
        runtime.scope_registry.push(scope);
    });
}
fn call(name: &str, args: Vec<Handle>) -> Handle {
    let (callable, arguments) = with_runtime(|runtime| {
        (
            runtime.allocate(Object::Builtin(name.into())).unwrap(),
            runtime.allocate(Object::Tuple(args)).unwrap(),
        )
    });
    let continuation = Handle(ril_rt_cps_end());
    let step = dispatch(callable, arguments, continuation).unwrap();
    assert_ne!(
        step,
        0,
        "{:?}",
        with_runtime(|runtime| runtime.fault.clone())
    );
    with_runtime(|runtime| match runtime.heap.get(Handle(step)).unwrap() {
        Object::CpsStep(Step::Return { value, .. }) => *value,
        value => panic!("unexpected channel step {value:?}"),
    })
}

#[test]
fn native_dispatch_keeps_channel_results_and_closed_tags_distinct() {
    fixture();
    let capacity = with_runtime(|runtime| runtime.int(1).unwrap());
    let pair = call("Channel::__bounded_0_1_2", vec![capacity]);
    let values = with_runtime(|runtime| runtime.sequence(pair).unwrap());
    let (tx, rx) = (values[0], values[1]);
    let number = with_runtime(|runtime| runtime.int(42).unwrap());
    let sent = call("Channel::send", vec![tx, number]);
    assert!(with_runtime(
        |runtime| matches!(runtime.heap.get(sent).unwrap(), Object::Variant { tag, .. } if tag == "Ok")
    ));
    call("Channel::close", vec![tx]);
    let received = call("Channel::recv", vec![rx]);
    assert!(with_runtime(
        |runtime| matches!(runtime.heap.get(received).unwrap(), Object::Variant { tag, fields } if tag == "Ok" && fields == &[number])
    ));
    let closed = call("Channel::recv", vec![rx]);
    let error = with_runtime(|runtime| match runtime.heap.get(closed).unwrap() {
        Object::Variant { tag, fields } if tag == "Err" => fields[0],
        value => panic!("expected closed error {value:?}"),
    });
    assert!(with_runtime(
        |runtime| matches!(runtime.heap.get(error).unwrap(), Object::Variant { tag, .. } if tag == "Channel::ChannelError::Closed")
    ));
}

#[test]
fn cancellation_before_send_dispatch_still_consumes_and_closes_detached_payload() {
    fixture();
    let (callable, args, continuation, ticket, payload_rx, context) = with_runtime(|runtime| {
        let control = runtime.create_channel(1).unwrap();
        let control = runtime.sequence(control).unwrap();
        let payload = runtime.create_channel(1).unwrap();
        let payload = runtime.sequence(payload).unwrap();
        let ticket = runtime
            .channel_endpoint(payload[0])
            .unwrap()
            .detach(runtime.channel_context())
            .unwrap();
        let managed_ticket = runtime.allocate_channel_ticket(ticket.clone()).unwrap();
        let callable = runtime
            .allocate(Object::Builtin("Channel::send".into()))
            .unwrap();
        let args = runtime
            .allocate(Object::Tuple(vec![control[0], managed_ticket]))
            .unwrap();
        let Object::ChannelReceiver(payload_rx) = runtime.heap.get(payload[1]).unwrap() else {
            panic!("receiver");
        };
        (
            callable,
            args,
            Handle::INVALID,
            ticket,
            payload_rx.clone(),
            CallContext::from_runtime(runtime),
        )
    });
    context.cancellation.request();
    assert_eq!(dispatch(callable, args, continuation), Some(0));
    assert_eq!(
        with_runtime(|runtime| runtime.fault.as_ref().unwrap().tag),
        OutcomeTag::Cancelled
    );
    assert!(ticket.attach(context.authority()).is_err());
    assert!(
        payload_rx
            .recv(context.authority(), &Cancellation::default())
            .unwrap()
            .is_none()
    );
}

#[test]
fn pre_cancelled_submitted_send_consumes_receiver_through_the_complete_trampoline() {
    for callback_entry in [false, true] {
        fixture();
        let (callable, args, ticket, payload_sender, control_sender, unit, context) =
            with_runtime(|runtime| {
                // This fixture has a scope registry for authority validation,
                // but no ActiveScope whose cancellation cleanup could hide an
                // early trampoline exit that never submitted the send.
                assert!(runtime.concurrent_scopes.is_empty());
                let control = runtime.create_channel(1).unwrap();
                let control = runtime.sequence(control).unwrap();
                let payload = runtime.create_channel(1).unwrap();
                let payload = runtime.sequence(payload).unwrap();
                let ticket = runtime
                    .channel_endpoint(payload[1])
                    .unwrap()
                    .detach(runtime.channel_context())
                    .unwrap();
                let managed_ticket = runtime.allocate_channel_ticket(ticket.clone()).unwrap();
                let callable = runtime
                    .allocate(Object::Builtin("Channel::send".into()))
                    .unwrap();
                let args = runtime
                    .allocate(Object::Tuple(vec![control[0], managed_ticket]))
                    .unwrap();
                let unit = runtime.unit().unwrap();
                let Object::ChannelSender(payload_sender) = runtime.heap.get(payload[0]).unwrap()
                else {
                    panic!("payload sender");
                };
                let Object::ChannelSender(control_sender) = runtime.heap.get(control[0]).unwrap()
                else {
                    panic!("control sender");
                };
                (
                    callable,
                    args,
                    ticket,
                    payload_sender.clone(),
                    control_sender.clone(),
                    unit,
                    CallContext::from_runtime(runtime),
                )
            });
        let end = ril_rt_cps_end();
        assert_ne!(end, 0);
        context.cancellation.request();
        let initial = if callback_entry {
            ril_rt_cps_callback_call(callable.0, args.0, end)
        } else {
            ril_rt_cps_call(callable.0, args.0, end)
        };
        assert_ne!(initial, 0, "call plumbing must preserve the submitted send");
        assert_eq!(ril_rt_cps_run(initial), 0);
        assert_eq!(
            with_runtime(|runtime| runtime.fault.as_ref().unwrap().tag),
            OutcomeTag::Cancelled
        );
        assert!(ticket.attach(context.authority()).is_err());
        let uncancelled = Cancellation::default();
        assert!(
            !payload_sender
                .send(
                    context.authority(),
                    Message::new(unit, vec![]),
                    &uncancelled
                )
                .unwrap(),
            "the submitted Receiver must actually be closed"
        );
        assert!(
            control_sender
                .send(
                    context.authority(),
                    Message::new(unit, vec![]),
                    &uncancelled
                )
                .unwrap(),
            "scope cleanup must not provide a false positive by closing every channel"
        );
        assert!(with_runtime(|runtime| runtime.concurrent_scopes.is_empty()));
        control_sender.close_in_scope(control_sender.scope_id());
        payload_sender.close_in_scope(payload_sender.scope_id());
    }
}

#[test]
fn cancelled_receive_publication_discards_its_receipt_outside_the_heap_gate() {
    fixture();
    let (sender, receiver, message, payload_rx, context) = with_runtime(|runtime| {
        let control = runtime.create_channel(1).unwrap();
        let control = runtime.sequence(control).unwrap();
        let payload = runtime.create_channel(1).unwrap();
        let payload = runtime.sequence(payload).unwrap();
        let ticket = runtime
            .channel_endpoint(payload[0])
            .unwrap()
            .detach(runtime.channel_context())
            .unwrap();
        let ticket = runtime.allocate_channel_ticket(ticket).unwrap();
        let message = Message::new(ticket, runtime.channel_tickets(ticket).unwrap());
        let Object::ChannelSender(sender) = runtime.heap.get(control[0]).unwrap() else {
            panic!("sender");
        };
        let Object::ChannelReceiver(receiver) = runtime.heap.get(control[1]).unwrap() else {
            panic!("receiver");
        };
        let Object::ChannelReceiver(payload_rx) = runtime.heap.get(payload[1]).unwrap() else {
            panic!("payload receiver");
        };
        (
            sender.clone(),
            receiver.clone(),
            message,
            payload_rx.clone(),
            CallContext::from_runtime(runtime),
        )
    });
    sender
        .send(context.authority(), message, &context.cancellation)
        .unwrap();
    let receipt = receiver
        .recv(context.authority(), &context.cancellation)
        .unwrap()
        .unwrap();
    context.cancellation.request();
    assert_eq!(finish_receive(receipt, Handle::INVALID), 0);
    assert!(receiver.references().is_empty());
    assert!(
        payload_rx
            .recv(context.authority(), &Cancellation::default())
            .unwrap()
            .is_none()
    );
}
