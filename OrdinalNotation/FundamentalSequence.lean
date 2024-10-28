import Mathlib.SetTheory.Ordinal.Arithmetic

universe u

namespace Ordinal

variable {α : Type u} [Preorder α]

/-- The type of sequences with length 0, 1, or `ω`. -/
def Sequence (α : Type u) : Type u :=
  Option α ⊕ (ℕ → α)

namespace Sequence

/-- The empty sequence, whose limit is the bottom element. -/
instance : EmptyCollection (Sequence α) :=
  ⟨Sum.inl none⟩

instance : Inhabited (Sequence α) :=
  ⟨∅⟩

/-- The sequence consisting only of `x`, whose limit is the succesor of `x`. -/
def ofElement (x : α) : Sequence α :=
  Sum.inl (some x)

/-- A sequence `ℕ → α`, whose limit is its supremum. -/
def ofNat (f : ℕ → α) : Sequence α :=
  Sum.inr f

/-- A sequence of length `0` or `1` is always strictly monotonic. For a sequence of length `ω`,
`StrictMono` just reduces to the usual predicate. -/
def StrictMono : Sequence α → Prop
  | Sum.inl _ => true
  | Sum.inr f => _root_.StrictMono f

theorem strictMono_empty : StrictMono (∅ : Sequence α) := rfl
theorem strictMono_ofElement (x : α) : StrictMono (ofElement x) := rfl
@[simp] theorem strictMono_ofNat {f : ℕ → α} : StrictMono (ofNat f) ↔ _root_.StrictMono f := Iff.rfl

/-- The limit of a sequence is the value to which it converges.

For length 0 sequences, we say that the bottom element is their limit. For length 1 sequences `x`,
we say that their limit is the successor of `x`. -/
def IsLimit : Sequence α → α → Prop
  | Sum.inl none, x => IsMin x
  | Sum.inl (some x), y => x ⋖ y
  | Sum.inr f, y => ∀ {x}, x < y ↔ ∃ n, x < f n

@[simp] theorem isLimit_empty {x : α} : IsLimit ∅ x ↔ IsMin x := Iff.rfl
@[simp] theorem isLimit_ofElement {x y : α} : IsLimit (ofElement x) y ↔ x ⋖ y := Iff.rfl
theorem isLimit_ofNat {f : ℕ → α} : IsLimit (ofNat f) y ↔ ∀ x, x < y ↔ (∃ n, x < f n) := Iff.rfl

theorem lt_of_strictMono_of_isLimit {f : ℕ → α} (hs : StrictMono (ofNat f))
    {x : α} (hl : IsLimit (ofNat f) x) (n : ℕ) : f n < x :=
  hl.2 ⟨_, hs (n.lt_succ_self)⟩

end Sequence

open Sequence

/-- A fundamental sequence is a `Sequence` (with length 0, 1, or `ω`) which is strictly monotonic
and converges to `top`. -/
structure FundamentalSequence (top : α) : Type u where
  /-- The underlying `Sequence` -/
  sequence : Sequence α
  /-- A fundamental sequence is strictly monotonic -/
  strictMono : sequence.StrictMono
  /-- The fundamental sequence converges at `top` -/
  limit_eq : sequence.IsLimit top

/-- Given a minimal element, the empty sequence is a fundamental sequence for it. -/
def FundamentalSequence.ofIsMin {x : α} (hx : IsMin x) : FundamentalSequence x :=
  ⟨∅, strictMono_empty, isLimit_empty.2 hx⟩

/-- If `y` covers `x`, then `x` is a fundamental sequence for `y`. -/
def FundamentalSequence.ofCovby {x y : α} (h : x ⋖ y) : FundamentalSequence y :=
  ⟨_, strictMono_ofElement x, Sequence.isLimit_ofElement.2 h⟩

/-- A fundamental sequence system is a set of `FundamentalSequence`, one for each element of the
order. -/
def FundamentalSequenceSystem (α : Type u) [Preorder α] : Type u :=
  ∀ top : α, FundamentalSequence top

example : FundamentalSequenceSystem ℕ
  | 0 => FundamentalSequence.ofIsMin isMin_bot
  | n + 1 => FundamentalSequence.ofCovby (Order.covBy_add_one n)

/-- An auxiliary definition for `slowGrowing` and `fastGrowing`. The function `g` describes what
happens at the successor step. -/
private def growingAux (s : FundamentalSequenceSystem α) [WellFoundedLT α]
    (x : α) (g : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) : ℕ :=
  match s x with
  | ⟨Sum.inl none, _, _⟩ => n + 1
  | ⟨Sum.inl (some y), _, h⟩ => have := h.lt; g (growingAux s y g) n
  | ⟨Sum.inr f, hs, hl⟩ => have := lt_of_strictMono_of_isLimit hs hl n; growingAux s (f n) g n
termination_by wellFounded_lt.wrap x

/-- The slow growing hierarchy, given a fundamental sequence system `s`, is defined as follows:
* `fastGrowing s ⊥ n = n + 1`
* `fastGrowing s (succ x) n = fastGrowing s x n + 1`
* `fastGrowing s x n = fastGrowing s (f n) n`, where `f` is the fundamental sequence converging to
  the limit `x`.
-/
def slowGrowing (s : FundamentalSequenceSystem α) [WellFoundedLT α] (x : α) : ℕ → ℕ :=
  growingAux s x fun f n ↦ f n + 1

/-- The fast growing hierarchy, given a fundamental sequence system `s`, is defined as follows:
* `fastGrowing s ⊥ n = n + 1`
* `fastGrowing s (succ x) n = (fastGrowing s x)^[n] n`
* `fastGrowing s x n = fastGrowing s (f n) n`, where `f` is the fundamental sequence converging to
  the limit `x`.
-/
def fastGrowing (s : FundamentalSequenceSystem α) [WellFoundedLT α] (x : α) : ℕ → ℕ :=
  growingAux s x fun f n ↦ f^[n] n

end Ordinal
