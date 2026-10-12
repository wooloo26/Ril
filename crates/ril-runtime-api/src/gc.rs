use crate::Unavailable;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectId(pub u64);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeDescriptorId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RootId(pub u64);
/// Roots are explicit and traceable, including roots held by suspended computations.
pub trait ManagedHeap {
    fn allocate(&mut self, ty: TypeDescriptorId) -> Result<ObjectId, Unavailable>;
    fn register_root(&mut self, object: ObjectId) -> Result<RootId, Unavailable>;
    fn unregister_root(&mut self, root: RootId) -> Result<(), Unavailable>;
    fn trace(&self, object: ObjectId, visitor: &mut dyn FnMut(ObjectId))
    -> Result<(), Unavailable>;
    fn safepoint(&mut self) -> Result<(), Unavailable>;
}
