import Mathlib.SetTheory.Ordinal.Arithmetic

universe u

variable {α : Type u} {x y : α}

namespace Ordinal

/-- An ordinal notation is a principal segment of the ordinals with a decidable ordering.

Usually, one first constructs a larger type of terms, of which a certain subtype of "normal forms"
satisfies the appropriate conditions. -/
class Notation (α : Type*) [LinearOrder α] where
  /-- Represent a term as an ordinal. -/
  repr : α <i Ordinal.{0}

namespace Notation

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

theorem mem_range_repr_iff_lt {o : Ordinal} : o ∈ Set.range (repr : α → _) ↔ o < top α :=
  repr.mem_range_iff_rel' o

end Notation


end Ordinal
