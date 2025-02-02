/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Ordinal notations

This file defines a typeclass for ordinal notations, which can be used to easily infer or define all
of the appropriate typeclasses of an initial segment of the ordinals.
-/

variable {α : Type*} {x y : α}

open Order Set

namespace Ordinal

/-! ### Notation class -/

/-- An ordinal notation is a principal segment of the ordinals with a decidable ordering.

Usually, one first constructs a larger type of terms, of which a certain subtype of "normal forms"
satisfies the appropriate conditions. -/
class Notation (α : Type*) [LinearOrder α] extends Zero α, One α where
  /-- Represent a term as an ordinal. -/
  repr : α <i Ordinal.{0}
  repr_zero : repr 0 = 0 := by simp
  repr_one : repr 1 = 1 := by simp

namespace Notation

attribute [simp] repr_zero repr_one

/-- Construct a linear order from a principal segment into the ordinals. -/
def linearOrderOfRepr (lt : α → α → Prop) [DecidableRel lt]
    (repr : lt ≺i (· < · : Ordinal → Ordinal → Prop)) : LinearOrder α :=
  have : IsStrictTotalOrder α lt :=
    { irrefl a := by
        rw [← repr.map_rel_iff']
        exact lt_irrefl _
      trichotomous a b := by
        rw [← repr.map_rel_iff', ← repr.inj, ← repr.map_rel_iff']
        exact lt_trichotomy _ _
      trans a b c := by
        rw [← repr.map_rel_iff', ← repr.map_rel_iff', ← repr.map_rel_iff']
        exact lt_trans }
  linearOrderOfSTO lt

variable [LinearOrder α] [Notation α]

/-- The smallest ordinal not represented by an ordinal notation. -/
def top (α : Type*) [LinearOrder α] [h : Notation α] : Ordinal.{0} := h.repr.top

theorem repr_le_repr : repr x ≤ repr y ↔ x ≤ y := repr.le_iff_le
theorem repr_lt_repr : repr x < repr y ↔ x < y := repr.lt_iff_lt
theorem repr_inj : repr x = repr y ↔ x = y := repr.inj
theorem repr_lt_top (x : α) : repr x < top α := repr.lt_top x
theorem mem_range_repr_iff_lt {o : Ordinal} : o ∈ range (repr : α → _) ↔ o < top α :=
  repr.mem_range_iff_rel' o

-- We can use `WellFoundedLT.conditionallyCompleteLinearOrderBot` to (nonconstructibly) define
-- infima and suprema.
instance : WellFoundedLT α := repr.isWellFounded

theorem isSuccLimit_top [NoMaxOrder α] : IsSuccLimit (top α) := by
  refine ⟨(repr_lt_top 0).not_isMin, fun a ha ↦ ?_⟩
  obtain ⟨b, rfl⟩ := mem_range_repr_iff_lt.2 ha.lt
  obtain ⟨c, hc⟩ := exists_gt b
  rw [← repr_lt_repr] at hc
  exact (ha.ge_of_gt hc).not_lt (repr_lt_top c)

/-! ### Lawful operation classes -/

/-- An ordinal notation with a correct addition operation. -/
class LawfulAdd (α : Type*) [LinearOrder α] [Notation α] [Add α] where
  repr_add (x y : α) : repr (x + y) = repr x + repr y
export LawfulAdd (repr_add)

/-- An ordinal notation with a correct subtraction operation. -/
class LawfulSub (α : Type*) [LinearOrder α] [Notation α] [Sub α] where
  repr_sub (x y : α) : repr (x - y) = repr x - repr y
export LawfulSub (repr_sub)

/-- An ordinal notation with a correct multiplication operation. -/
class LawfulMul (α : Type*) [LinearOrder α] [Notation α] [Mul α] where
  repr_mul (x y : α) : repr (x * y) = repr x * repr y
export LawfulMul (repr_mul)

/-- An ordinal notation with a correct division operation. -/
class LawfulDiv (α : Type*) [LinearOrder α] [Notation α] [Div α] where
  repr_div (x y : α) : repr (x / y) = repr x / repr y
export LawfulDiv (repr_div)

/-- An ordinal notation with a correct exponentiation operation. -/
class LawfulPow (α : Type*) [LinearOrder α] [Notation α] [Pow α α] where
  repr_pow (x y : α) : repr (x ^ y) = repr x ^ repr y
export LawfulPow (repr_pow)

attribute [simp] repr_add repr_sub repr_mul repr_div repr_pow

section Add
variable [LinearOrder α] [Notation α] [Add α] [LawfulAdd α]

instance instNoMaxOrderOfAdd : NoMaxOrder α where
  exists_gt a := by
    use a + 1
    rw [← repr_lt_repr, repr_add, repr_one]
    exact lt_add_one _

/-- An ordinal notation is a `SuccOrder` setting `succ x = x + 1`. -/
def toSuccAddOrder (α : Type*) [LinearOrder α] [Notation α] [Add α] [LawfulAdd α] :
    SuccAddOrder α := by
  letI : SuccOrder α := by
    refine SuccOrder.ofCore (· + 1) ?_ fun a ha ↦ (not_isMax _ ha).elim
    intro a ha b
    rw [← repr_lt_repr, ← add_one_le_iff, ← @repr_one α, ← repr_add, repr_le_repr]
  exact ⟨fun _ ↦ rfl⟩

end Add

end Notation
end Ordinal
