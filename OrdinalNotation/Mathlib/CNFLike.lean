import OrdinalNotation.Basic
import Mathlib.Data.Prod.Lex

universe u

open Ordinal Set

section CNFList
variable {E : Type u} [LinearOrder E]

/-- A list of exponents in `E` and coefficients in `ℕ+`, with the exponents in decreasing order.
This emulates a construction of the form `ω ^ e₀ * n₀ + ω ^ e₁ * n₁ + ⋯`, like the Cantor normal
form.

If `E` is an ordinal notation, then `CNFList` can also be given the structure of an ordinal
notation. Moreover, we can define arithmetic on this type through simpler arithmetic on `E`. -/
def CNFList (E : Type u) [LinearOrder E] : Type u :=
  Subtype fun l : List (E ×ₗ ℕ+) ↦ (l.map fun x ↦ (ofLex x).1).Sorted (· > ·)

instance : Zero (CNFList E) := ⟨⟨[], List.sorted_nil⟩⟩
instance [Zero E] : One (CNFList E) := ⟨⟨[toLex (0, 1)], List.sorted_singleton _⟩⟩
instance : LinearOrder (CNFList E) := Subtype.instLinearOrder _

@[simp] theorem zero_val : (0 : CNFList E).val = [] := rfl
@[simp] theorem one_val [Zero E] : (1 : CNFList E).val = [toLex (0, 1)] := rfl

noncomputable instance [Notation E] : Notation (CNFList E) where
  repr := by
    let f (l : CNFList E) := (l.1.map fun x ↦ ω ^ Notation.repr (ofLex x).1 * (ofLex x).2).sum
    refine ⟨(OrderEmbedding.ofStrictMono f ?_).ltEmbedding, ω ^ Notation.top E, ?_⟩
    · sorry
    · sorry
  repr_zero := List.sum_nil
  repr_one := by simp

end CNFList

/-- A type which is order-isomorphic to `CNFList Exp` for some type of exponents. -/
class CNFLike (α : Type u) extends Zero α, One α, LinearOrder α where
  /-- The type of exponents in the Cantor form. -/
  Exp : Type u
  /-- Exponents are linearly ordered. -/
  linearOrderExp : LinearOrder Exp
  /-- Exponents form an ordinal notation. -/
  notationExp : Notation Exp

  /-- The type is order-isomorphic to `CNFList Exp`. -/
  equivList : α ≃o CNFList Exp
  equivList_zero : equivList 0 = 0
  equivList_one : equivList 1 = 1

namespace CNFLike
variable [CNFLike α]

attribute [instance] linearOrderExp notationExp
attribute [simp] equivList_zero equivList_one

noncomputable instance : Notation α where
  repr := equivList.toInitialSeg.transPrincipal Notation.repr

end CNFLike
