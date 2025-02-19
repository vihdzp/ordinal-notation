/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Exponential
import OrdinalNotation.Mathlib.Lemmas

/-!
# Ordinal notations

This file defines a typeclass for ordinal notations, which can be used to easily infer or define all
of the appropriate typeclasses of an initial segment of the ordinals.
-/

variable {α : Type*} {x y : α}

open Order Set

namespace Ordinal

/-! ### Notation class -/

/-- An ordinal notation is a principal segment of the ordinals with decidable ordering.

Usually, one first constructs a larger type of terms, of which a certain subtype of "normal forms"
satisfies the appropriate conditions. -/
class Notation (α : Type*) [LinearOrder α] extends Zero α, One α where
  /-- Represent a term as an ordinal. -/
  eval : α <i Ordinal.{0}
  eval_zero : eval 0 = 0 := by simp
  eval_one : eval 1 = 1 := by simp

namespace Notation

attribute [simp] eval_zero eval_one

/-- Construct a linear order from a principal segment into the ordinals. -/
def linearOrderOfRepr (lt : α → α → Prop) [DecidableRel lt]
    (eval : lt ≺i (· < · : Ordinal → Ordinal → Prop)) : LinearOrder α :=
  have : IsStrictTotalOrder α lt :=
    { irrefl a := by
        rw [← eval.map_rel_iff']
        exact lt_irrefl _
      trichotomous a b := by
        rw [← eval.map_rel_iff', ← eval.inj, ← eval.map_rel_iff']
        exact lt_trichotomy _ _
      trans a b c := by
        rw [← eval.map_rel_iff', ← eval.map_rel_iff', ← eval.map_rel_iff']
        exact lt_trans }
  linearOrderOfSTO lt

variable [LinearOrder α] [Notation α]

/-- The smallest ordinal not evalesented by an ordinal notation. -/
def top (α : Type*) [LinearOrder α] [h : Notation α] : Ordinal.{0} := h.eval.top

theorem eval_strictMono : StrictMono (eval : α → _) := eval.strictMono
theorem eval_monotone : Monotone (eval : α → _) := eval.monotone
theorem eval_le_eval : eval x ≤ eval y ↔ x ≤ y := eval.le_iff_le
theorem eval_lt_eval : eval x < eval y ↔ x < y := eval.lt_iff_lt
theorem eval_inj : eval x = eval y ↔ x = y := eval.inj
theorem eval_lt_top (x : α) : eval x < top α := eval.lt_top x
theorem range_eval : range (eval : α → _) = Set.Iio (top α) := eval.range_eq_Iio_top

@[simp] theorem eval_eq_zero_iff : eval (x : α) = 0 ↔ x = 0 :=
  eval_zero (α := α) ▸ eval_inj (y := 0)
@[simp] theorem eval_eq_one_iff : eval (x : α) = 1 ↔ x = 1 :=
  eval_one (α := α) ▸ eval_inj (y := 1)

theorem mem_range_eval_iff_lt {o : Ordinal} : o ∈ range (eval : α → _) ↔ o < top α :=
  eval.mem_range_iff_rel' o

theorem mem_range_eval_of_le {o} {x : α} : o ≤ eval x → o ∈ Set.range (eval : α → _) :=
  eval.mem_range_of_le

instance : OrderBot α where
  bot := 0
  bot_le x := by
    rw [← eval_le_eval]
    exact eval_zero.trans_le (Ordinal.zero_le _)

@[simp] theorem bot_eq_zero : (⊥ : α) = 0 := rfl

-- We can use `WellFoundedLT.conditionallyCompleteLinearOrderBot` to (nonconstructibly) define
-- infima and suprema.
instance : WellFoundedLT α := eval.isWellFounded

theorem isSuccLimit_top [NoMaxOrder α] : IsSuccLimit (top α) := by
  refine ⟨(eval_lt_top 0).not_isMin, fun a ha ↦ ?_⟩
  obtain ⟨b, rfl⟩ := mem_range_eval_iff_lt.2 ha.lt
  obtain ⟨c, hc⟩ := exists_gt b
  rw [← eval_lt_eval] at hc
  exact (ha.ge_of_gt hc).not_lt (eval_lt_top c)

/-! ### Lawful operation classes -/

/-- An ordinal notation with a correct cast into naturals. -/
class LawfulNatCast (α : Type*) [LinearOrder α] [Notation α] [NatCast α] where
  eval_natCast (n : ℕ) : eval (n : α) = n
export LawfulNatCast (eval_natCast)

/-- An ordinal notation with a correct addition operation. -/
class LawfulAdd (α : Type*) [LinearOrder α] [Notation α] [Add α] where
  eval_add (x y : α) : eval (x + y) = eval x + eval y
export LawfulAdd (eval_add)

/-- An ordinal notation with a correct subtraction operation. -/
class LawfulSub (α : Type*) [LinearOrder α] [Notation α] [Sub α] where
  eval_sub (x y : α) : eval (x - y) = eval x - eval y
export LawfulSub (eval_sub)

/-- An ordinal notation with a correct multiplication operation. -/
class LawfulMul (α : Type*) [LinearOrder α] [Notation α] [Mul α] where
  eval_mul (x y : α) : eval (x * y) = eval x * eval y
export LawfulMul (eval_mul)

/-- An ordinal notation with a correct division operation. -/
class LawfulDiv (α : Type*) [LinearOrder α] [Notation α] [Div α] where
  eval_div (x y : α) : eval (x / y) = eval x / eval y
export LawfulDiv (eval_div)

/-- An ordinal notation with a correct exponentiation operation. -/
class LawfulPow (α : Type*) [LinearOrder α] [Notation α] [Pow α α] where
  eval_pow (x y : α) : eval (x ^ y) = eval x ^ eval y
export LawfulPow (eval_pow)

attribute [simp] eval_natCast eval_add eval_sub eval_mul eval_div eval_pow

section Add
variable [Add α] [LawfulAdd α]

instance : AddMonoidWithOne α where
  add_assoc a b c := by rw [← eval_inj, eval_add]; simp [add_assoc]
  zero_add a := by rw [← eval_inj]; simp
  add_zero a := by rw [← eval_inj]; simp
  nsmul := nsmulRec

instance : CanonicallyOrderedAdd α where
  exists_add_of_le {a b} h := by
    obtain ⟨c, hc⟩ := mem_range_eval_of_le (Ordinal.sub_le_self (eval b) (eval a))
    use c
    rw [← eval_inj, eval_add, hc, Ordinal.add_sub_cancel_of_le]
    simpa
  le_self_add a b := by
    rw [← eval_le_eval, eval_add]
    exact le_self_add

instance : AddLeftMono α where
  elim a b c := by rw [← eval_le_eval, ← eval_le_eval (x := a + b)]; simp
instance : AddLeftReflectLE α where
  elim a b c := by rw [← eval_le_eval, ← eval_le_eval (x := b)]; simp
instance : AddLeftStrictMono α where
  elim a b c := by rw [← eval_lt_eval, ← eval_lt_eval (x := a + b)]; simp
instance : AddLeftReflectLT α where
  elim a b c := by rw [← eval_lt_eval, ← eval_lt_eval (x := b)]; simp

instance : AddRightMono α where
  elim a b c := by
    rw [← eval_le_eval, ← eval_le_eval (x := b + a)]
    simpa [- PrincipalSeg.le_iff_le] using (add_le_add_right · _)

instance : AddRightReflectLT α where
  elim a b c := by
    rw [← eval_lt_eval, ← eval_lt_eval (x := b)]
    simpa [- PrincipalSeg.lt_iff_lt] using lt_of_add_lt_add_right

instance : NoMaxOrder α where
  exists_gt a := by
    use a + 1
    rw [← eval_lt_eval, eval_add, eval_one]
    exact lt_add_one _

/-- An ordinal notation is a `SuccOrder` setting `succ x = x + 1`. -/
instance (α : Type*) [LinearOrder α] [Notation α] [Add α] [LawfulAdd α] : SuccAddOrder α :=
  let _ : SuccOrder α := by
    refine SuccOrder.ofCore (· + 1) ?_ fun a ha ↦ (not_isMax _ ha).elim
    intro a ha b
    rw [← eval_lt_eval, ← add_one_le_iff, ← @eval_one α, ← eval_add, eval_le_eval]
  ⟨fun _ ↦ rfl⟩

end Add

section Sub
variable [Sub α] [LawfulSub α]

@[simp]
theorem sub_eq_zero_iff_le {a b : α} : a - b = 0 ↔ a ≤ b := by
  rw [← eval_inj]
  simp [Ordinal.sub_eq_zero_iff_le]

theorem sub_ne_zero_iff_lt {a b : α} : a - b ≠ 0 ↔ b < a := by
  simp

@[simp]
theorem sub_pos_iff_lt {a b : α} : 0 < a - b ↔ b < a := by
  rw [← eval_lt_eval]
  simp [Ordinal.pos_iff_ne_zero, Ordinal.sub_eq_zero_iff_le]

@[simp] theorem sub_zero (a : α) : a - 0 = a := by rw [← eval_inj]; simp
@[simp] theorem zero_sub (a : α) : 0 - a = 0 := by simpa using bot_le (a := a)
@[simp] theorem sub_self (a : α) : a - a = 0 := by simp

end Sub

section Mul
variable [Mul α] [LawfulMul α]

instance : MulZeroClass α where
  zero_mul a := by rw [← eval_inj]; simp
  mul_zero a := by rw [← eval_inj]; simp

instance [Add α] [LawfulAdd α] : LeftDistribClass α where
  left_distrib a b c := by rw [← eval_inj]; simp [mul_add]

end Mul

section Div
variable [Div α] [LawfulDiv α]

@[simp]
theorem zero_div (a : α) : 0 / a = 0 := by
  rw [← eval_inj]; simp

@[simp]
theorem div_zero (a : α) : a / 0 = 0 := by
  rw [← eval_inj]; simp

end Div

/-! ### Examples -/

/-! #### Extending a notation by one element -/

/-- An ordinal notation on `α` may be extended to `WithTop α`. -/
instance [LinearOrder α] [Notation α] : Notation (WithTop α) where
  eval := eval.withTop
  eval_zero := eval_zero
  eval_one := eval_one

/-! #### The natural numbers-/

/-- The naturals can be seen as an ordinal notation up to `ω`. -/
instance : Notation ℕ where
  eval := PrincipalSeg.natCast_ordinal

instance : LawfulNatCast ℕ where eval_natCast _ := rfl
instance : LawfulAdd ℕ where eval_add := Nat.cast_add
instance : LawfulSub ℕ where eval_sub := Ordinal.natCast_sub
instance : LawfulMul ℕ where eval_mul := Ordinal.natCast_mul
instance : LawfulDiv ℕ where eval_div := Ordinal.natCast_div
instance : LawfulPow ℕ where eval_pow := Ordinal.natCast_opow

end Notation
end Ordinal
