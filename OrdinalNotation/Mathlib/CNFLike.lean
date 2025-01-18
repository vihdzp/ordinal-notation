import OrdinalNotation.Basic

universe u

open Ordinal Set

/-- A type which emulates a construction of the form `ω ^ e₀ * n₀ + ω ^ e₁ * n₁ + ⋯`, like the
Cantor normal form.

This type must be isomorphic to a `List (Exp × ℕ+)` for some type `Exp` of exponents (which can be
defined in terms of the type itself). Furthermore, there must be normal forms for the exponents,
which are themselves linearly ordered and embed as a principal segment into the ordinals. -/
class CNFLike (α : Type u) extends Zero α where
  Exp : Type u
  listEquiv : α ≃ List (Exp × ℕ+)
  listEquiv_zero : listEquiv 0 = []
  NF_exp : Exp → Prop
  linearOrderExp : LinearOrder (Subtype NF_exp)
  repr_exp : Subtype NF_exp <i Ordinal.{0}

namespace CNFLike
variable [CNFLike α]

attribute [simp] listEquiv_zero
attribute [instance] linearOrderExp

@[simp]
theorem listEquiv_symm_nil : listEquiv.symm [] = (0 : α) := by
  rw [Equiv.symm_apply_eq, listEquiv_zero]

/-- The pseudo-constructor `ω ^ e * n + a`. -/
def wadd (e : Exp α) (n : ℕ+) (a : α) : α :=
  listEquiv.symm (⟨e, n⟩ :: listEquiv a)

@[simp]
theorem listEquiv_wadd (e : Exp α) (n : ℕ+) (a : α) :
    listEquiv (wadd e n a) = ⟨e, n⟩ :: listEquiv a :=
  listEquiv.apply_symm_apply _

@[elab_as_elim]
def waddRecOn {p : α → Sort*} (x : α) (zero : p 0) (wadd : ∀ e n a, p a → p (wadd e n a)) : p x :=
  suffices ∀ l, p (listEquiv.symm l) from cast (by simp) (this (listEquiv x))
  List.rec (cast (by simp) zero) fun x l IH ↦ cast (by simp [CNFLike.wadd]) (wadd x.1 x.2 _ IH)

@[simp]
theorem waddRecOn_zero {p : α → Sort*} (zero : p 0) (wadd : ∀ e n a, p a → p (wadd e n a)) :
    waddRecOn 0 zero wadd = zero := by
  rw [waddRecOn, cast_eq_iff_heq, listEquiv_zero]
  exact cast_heq _ _

@[simp]
theorem cast_heq_iff_heq {α β γ : Sort u} (h : α = β) (a : α) (c : γ) :
    HEq (cast h a) c ↔ HEq a c := by
  subst h
  rfl

@[simp]
theorem heq_cast_iff_heq {α β γ : Sort u} (h : β = γ) (a : α) (b : β) :
    HEq a (cast h b) ↔ HEq a b := by
  subst h
  rfl

@[simp]
theorem waddRecOn_wadd {p : α → Sort*} (zero : p 0) (wadd : ∀ e n a, p a → p (wadd e n a))
    (e : Exp α) (n : ℕ+) (a : α) :
    waddRecOn (CNFLike.wadd e n a) zero wadd = wadd e n a (waddRecOn a zero wadd) := by
  rw [waddRecOn, cast_eq_iff_heq, listEquiv_wadd, cast_heq_iff_heq]
  congr
  · exact listEquiv.symm_apply_apply _
  · rw [waddRecOn, heq_cast_iff_heq]


end CNFLike
