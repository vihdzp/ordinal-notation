import Mathlib.SetTheory.Ordinal.Arithmetic

universe u

namespace Ordinal

variable {α : Type u} {β : Type*}

/-- The type of sequences with length 0, 1, or `ω`. -/
def Sequence (α : Type u) : Type u :=
  Option α ⊕ (ℕ → α)

namespace Sequence

/-- The empty sequence, whose limit is the bottom element. -/
instance : EmptyCollection (Sequence α) :=
  ⟨Sum.inl none⟩

instance : Inhabited (Sequence α) :=
  ⟨∅⟩

@[simp] theorem sum_inl_none_def : Sum.inl none = (∅ : Sequence α) := rfl

/-- The sequence consisting only of `x`, whose limit is the succesor of `x`. -/
instance : Singleton α (Sequence α) :=
  ⟨fun x ↦ Sum.inl (some x)⟩

@[simp] theorem sum_inl_some_def (x : α) : Sum.inl (some x) = ({x} : Sequence α) := rfl

/-- A sequence `ℕ → α`, whose limit is its supremum. -/
def ofFun (f : ℕ → α) : Sequence α :=
  Sum.inr f

@[simp] theorem sum_inr_def (f : ℕ → α) : Sum.inr f = ofFun f := rfl

/-- Membership predicate for sequences -/
def mem (s : Sequence α) (x : α) : Prop :=
  match s with
  | Sum.inl none => False
  | Sum.inl (some y) => x = y
  | Sum.inr f => x ∈ Set.range f

instance : Membership α (Sequence α) :=
  ⟨mem⟩

@[simp] theorem not_mem_empty (x : γ) : x ∉ (∅ : Sequence γ) := id
@[simp] theorem mem_singleton_iff {x y : γ} : x ∈ ({y} : Sequence γ) ↔ x = y := Iff.rfl
@[simp] theorem mem_ofFun_iff {x : γ} {f : ℕ → γ} : x ∈ ofFun f ↔ x ∈ Set.range f := Iff.rfl

/-- Maps a sequence through a function -/
def map (s : Sequence α) (g : α → β) : Sequence β :=
  match s with
  | Sum.inl none => ∅
  | Sum.inl (some x) => {g x}
  | Sum.inr f => ofFun (g ∘ f)

@[simp] theorem map_empty (g : α → β) : map ∅ g = ∅ := rfl
@[simp] theorem map_singleton (x : α) (g : α → β) : map {x} g = {g x} := rfl
@[simp] theorem map_ofFun (f : ℕ → α) (g : α → β) : map (ofFun f) g = ofFun (g ∘ f) := rfl

@[simp]
theorem mem_map {s : Sequence α} {f : α → β} {b : β} : b ∈ s.map f ↔ ∃ a, a ∈ s ∧ f a = b :=
  match s with
  | Sum.inl none => by simp
  | Sum.inl (some x) => by simp [eq_comm]
  | Sum.inr g => by simp

/-- Attach to a sequence the proof that it contains all its elements -/
def attach : (s : Sequence α) → Sequence {a : α // a ∈ s}
  | Sum.inl none => ∅
  | Sum.inl (some x) => {⟨x, rfl⟩}
  | Sum.inr f => ofFun fun n ↦ ⟨f n, Set.mem_range_self n⟩

/-- Builds a list with the first `n` elements of the sequence. This can be used to print the
sequence. -/
def toList (s : Sequence α) (n : ℕ) : List α :=
  match s with
  | Sum.inl none => []
  | Sum.inl (some x) => [x]
  | Sum.inr f => (List.range n).map f

variable [Preorder α] [Preorder β]

/-- A sequence of length `0` or `1` is always strictly monotonic. For a sequence of length `ω`,
`StrictMono` just reduces to the usual predicate. -/
protected def StrictMono : Sequence α → Prop
  | Sum.inl _ => true
  | Sum.inr f => _root_.StrictMono f

theorem strictMono_empty : (∅ : Sequence α).StrictMono := rfl
theorem strictMono_singleton (x : α) : ({x} : Sequence α).StrictMono := rfl
@[simp] theorem strictMono_ofFun {f : ℕ → α} : (ofFun f).StrictMono ↔ StrictMono f := Iff.rfl

theorem StrictMono.map {s : Sequence α} (hs : s.StrictMono) {g : α → β} (h : StrictMono g) :
    (s.map g).StrictMono :=
  match s with
  | Sum.inl none => rfl
  | Sum.inl (some _) => rfl
  | Sum.inr _ => h.comp hs

theorem StrictMono.attach {s : Sequence α} (hs : s.StrictMono) : s.attach.StrictMono :=
  match s with
  | Sum.inl none => rfl
  | Sum.inl (some _) => rfl
  | Sum.inr _ => fun _ _ h ↦ hs h

/-- The limit of a sequence is the value to which it converges.

For length 0 sequences, we say that the bottom element is their limit. For length 1 sequences `x`,
we say that their limit is the successor of `x`. -/
def IsLimit : Sequence α → α → Prop
  | Sum.inl none, x => IsMin x
  | Sum.inl (some x), y => x ⋖ y
  | Sum.inr f, y => ∀ {x}, x < y ↔ ∃ n, x < f n

@[simp] theorem isLimit_empty {x : α} : IsLimit ∅ x ↔ IsMin x := Iff.rfl
@[simp] theorem isLimit_ofElement {x y : α} : IsLimit {x} y ↔ x ⋖ y := Iff.rfl
theorem isLimit_ofFun {f : ℕ → α} : IsLimit (ofFun f) y ↔ ∀ x, x < y ↔ (∃ n, x < f n) := Iff.rfl

theorem lt_of_strictMono_of_isLimit {f : ℕ → α} (hs : (ofFun f).StrictMono)
    {x : α} (hl : IsLimit (ofFun f) x) (n : ℕ) : f n < x :=
  hl.2 ⟨_, hs (n.lt_succ_self)⟩

end Sequence

open Sequence

variable [Preorder α]

/-- A fundamental sequence is a `Sequence` (with length 0, 1, or `ω`) which is strictly monotonic
and converges to `top`. -/
structure FundamentalSequence (top : α) : Type u where
  /-- The underlying `Sequence` -/
  sequence : Sequence α
  /-- A fundamental sequence is strictly monotonic -/
  strictMono : sequence.StrictMono
  /-- The fundamental sequence converges at `top` -/
  limit_eq : sequence.IsLimit top

namespace FundamentalSequence

@[ext]
theorem ext (top : α) {f g : FundamentalSequence top} (h : f.sequence = g.sequence) : f = g := by
  cases f; cases g;
  simpa

/-- Given a minimal element, the empty sequence is a fundamental sequence for it. -/
@[simps]
def ofIsMin {x : α} (hx : IsMin x) : FundamentalSequence x :=
  ⟨∅, strictMono_empty, isLimit_empty.2 hx⟩

/-- The empty sequence is a fundamental sequence for `⊥`. -/
abbrev bot [OrderBot α] : FundamentalSequence (⊥ : α) :=
  FundamentalSequence.ofIsMin isMin_bot

/-- If `y` covers `x`, then `x` is a fundamental sequence for `y`. -/
@[simps]
def ofCovby {x y : α} (h : x ⋖ y) : FundamentalSequence y :=
  ⟨_, strictMono_singleton x, Sequence.isLimit_ofElement.2 h⟩

/-- `x` is a fundamental sequence for `succ x`. -/
abbrev succ (x : α) [SuccOrder α] [NoMaxOrder α] : FundamentalSequence (Order.succ x) :=
  FundamentalSequence.ofCovby (Order.covBy_succ x)

end FundamentalSequence

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
