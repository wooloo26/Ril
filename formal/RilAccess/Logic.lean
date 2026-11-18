import Std

namespace RilAccess

@[simp] theorem except_bind_ok (value : α) (f : α → Except ε β) :
    (Except.ok value >>= f) = f value := rfl
@[simp] theorem except_bind_error (error : ε) (f : α → Except ε β) :
    (Except.error error >>= f) = .error error := rfl
@[simp] theorem except_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Except ε α) = .ok (f value) := rfl
@[simp] theorem except_map_error (error : ε) (f : α → β) :
    f <$> (Except.error error : Except ε α) = .error error := rfl
@[simp] theorem except_pure (value : α) : (pure value : Except ε α) = .ok value := rfl

@[simp] theorem option_bind_some (value : α) (f : α → Option β) :
    (some value >>= f) = f value := rfl
@[simp] theorem option_bind_none (f : α → Option β) : (none >>= f) = none := rfl

end RilAccess
