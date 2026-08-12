/-!
A bijection with explicit inverse -- core has no such type; inspired by
Mathlib's `Equiv`. Dependency-free.
-/

namespace NearLinear4ct

/-- A bijection with explicit inverse (core has no `TypeEquiv` type). -/
structure TypeEquiv (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

namespace TypeEquiv

instance {α β : Type} : CoeFun (TypeEquiv α β) (fun _ => α → β) := ⟨toFun⟩

/-- The inverse bijection. -/
def symm {α β : Type} (e : TypeEquiv α β) : TypeEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

@[simp] theorem symm_apply_apply {α β : Type} (e : TypeEquiv α β) (a : α) :
    e.symm (e a) = a := e.left_inv a

@[simp] theorem apply_symm_apply {α β : Type} (e : TypeEquiv α β) (b : β) :
    e (e.symm b) = b := e.right_inv b

theorem injective {α β : Type} (e : TypeEquiv α β) {a a' : α} (h : e a = e a') :
    a = a' :=
  (e.left_inv a).symm.trans ((congrArg e.invFun h).trans (e.left_inv a'))

theorem eq_iff {α β : Type} (e : TypeEquiv α β) {a a' : α} :
    e a = e a' ↔ a = a' :=
  ⟨e.injective, fun h => congrArg e.toFun h⟩

@[simp] theorem symm_symm {α β : Type} (e : TypeEquiv α β) : e.symm.symm = e := rfl

/-- Compose two bijections. -/
def trans {α β γ : Type} (e₁ : TypeEquiv α β) (e₂ : TypeEquiv β γ) : TypeEquiv α γ where
  toFun a := e₂ (e₁ a)
  invFun c := e₁.invFun (e₂.invFun c)
  left_inv a := (congrArg e₁.invFun (e₂.left_inv (e₁ a))).trans (e₁.left_inv a)
  right_inv c := (congrArg e₂.toFun (e₁.right_inv (e₂.invFun c))).trans (e₂.right_inv c)

/-- Cast between equal-length index types. -/
def finCast {n m : Nat} (h : n = m) : TypeEquiv (Fin n) (Fin m) where
  toFun i := ⟨i.val, h ▸ i.isLt⟩
  invFun i := ⟨i.val, h ▸ i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem finCast_val {n m : Nat} (h : n = m) (i : Fin n) :
    ((finCast h).toFun i).val = i.val := rfl

end TypeEquiv
end NearLinear4ct
