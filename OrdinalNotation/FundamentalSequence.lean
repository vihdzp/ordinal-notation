import Mathlib.SetTheory.Ordinal.Arithmetic
import OrdinalNotation.ForMathlib

universe u

open Order

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

/-- Recursion on sequences, using the preferred forms of the constructors. -/
def recOn {p : Sequence α → Sort*} (s : Sequence α) (empty : p ∅) (singleton : ∀ x, p {x})
    (ofFun : ∀ f, p (ofFun f)) : p s :=
  match s with
  | Sum.inl none => empty
  | Sum.inl (some x) => singleton x
  | Sum.inr f => ofFun f

/-- Membership predicate for sequences -/
def mem (s : Sequence α) (x : α) : Prop :=
  match s with
  | Sum.inl none => False
  | Sum.inl (some y) => x = y
  | Sum.inr f => x ∈ Set.range f

instance : Membership α (Sequence α) :=
  ⟨mem⟩

@[simp] theorem not_mem_empty (x : α) : x ∉ (∅ : Sequence α) := id
@[simp] theorem mem_singleton_iff {x y : α} : x ∈ ({y} : Sequence α) ↔ x = y := Iff.rfl
@[simp] theorem mem_ofFun_iff {x : α} {f : ℕ → α} : x ∈ ofFun f ↔ x ∈ Set.range f := Iff.rfl

theorem mem_singleton (x : α) : x ∈ ({x} : Sequence α) := mem_singleton_iff.2 rfl

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

/-- The range of a sequence is the set of values it contains -/
def range : Sequence α → Set α
  | Sum.inl none => ∅
  | Sum.inl (some x) => {x}
  | Sum.inr f => Set.range f

@[simp] theorem range_empty : range (∅ : Sequence α) = ∅ := rfl
@[simp] theorem range_singleton (x : α) : range ({x} : Sequence α) = {x} := rfl
@[simp] theorem range_ofFun (f : ℕ → α) : range (ofFun f) = Set.range f := rfl

theorem mem_range_setOf {f : ℕ → α} (n : ℕ) : f n ∈ range (ofFun f) := ⟨n, rfl⟩

/-- Attach to a sequence the proof that it contains all its elements -/
def attach : (s : Sequence α) → Sequence {a : α // a ∈ s}
  | Sum.inl none => ∅
  | Sum.inl (some x) => {⟨x, rfl⟩}
  | Sum.inr f => ofFun fun n ↦ ⟨f n, Set.mem_range_self n⟩

/-- Partial map -/
def pmap {α β : Type*} (s : Sequence α) (f : ∀ x ∈ s, β) : Sequence β :=
  s.attach.map fun x ↦ f x.1 x.2

@[simp]
theorem pmap_empty {α β : Type*} (f : ∀ x ∈ (∅ : Sequence α), β) : pmap ∅ f = ∅ :=
  rfl

/-- `pmap_empty` but avoids type rewrites -/
theorem pmap_eq_empty_of_empty {α β : Type*} {s : Sequence α} (hs : s = ∅)
    (f : ∀ x ∈ s, β) : Sequence.pmap s f = ∅ := by
  subst hs
  rfl

@[simp]
theorem pmap_singleton {α β : Type*} (y : α) (f : ∀ x ∈ ({y} : Sequence α), β) :
    pmap _ f = {f y rfl} :=
  rfl

@[simp]
theorem pmap_ofFun {α β : Type*} (g : ℕ → α) (f : ∀ x ∈ ofFun g, β) :
    pmap _ f = ofFun fun n ↦ f (g n) (Set.mem_range_self _) :=
  rfl

/-- Builds a list with the first `n` elements of the sequence. This can be used to print the
sequence. -/
def toList (s : Sequence α) (n : ℕ) : List α :=
  match s with
  | Sum.inl none => []
  | Sum.inl (some x) => [x]
  | Sum.inr f => (List.range n).map f

section Preorder

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

/-- The limit of a sequence is the least value strictly greater than all its elements.

A length 0 sequence converges at a minimal element. A length 1 sequence `x` converges at the
successor of `x`. -/
def IsLimit (s : Sequence α) (y : α) : Prop :=
  ∀ {x}, x < y ↔ ∃ z ∈ range s, x ≤ z

end Preorder

section LinearOrder

variable [LinearOrder α] [LinearOrder β]

@[simp]
theorem isLimit_empty {x : α} : IsLimit ∅ x ↔ IsBot x := by
  simp [IsLimit, isBot_iff_isMin, isMin_iff_forall_not_lt]

alias ⟨IsLimit.isBot, isLimit_of_isBot⟩ := isLimit_empty

theorem isLimit_bot [OrderBot α] : IsLimit ∅ (⊥ : α) :=
  isLimit_of_isBot isBot_bot

@[simp]
theorem isLimit_singleton {x y : α} : IsLimit {x} y ↔ x ⋖ y := by
  simp [IsLimit, covBy_iff_lt_iff_le]

alias ⟨IsLimit.covBy, isLimit_of_covBy⟩ := isLimit_singleton

theorem isLimit_succ_of_not_isMax [SuccOrder α] {x : α} (h : ¬ IsMax x) : IsLimit {x} (succ x) :=
  isLimit_of_covBy (covBy_succ_of_not_isMax h)

theorem isLimit_succ [SuccOrder α] [NoMaxOrder α] (x : α) : IsLimit {x} (succ x) :=
  isLimit_succ_of_not_isMax (not_isMax x)

theorem isLimit_ofFun {f : ℕ → α} : IsLimit (ofFun f) y ↔ ∀ {x}, x < y ↔ ∃ n, x ≤ f n := by
  simp [IsLimit]

/-- A fundamental sequence for `x` is a strictly monotonic sequence with limit `x`. -/
structure IsFundamental (s : Sequence α) (x : α) : Prop where
  /-- A fundamental sequence is strictly monotonic -/
  strictMono : s.StrictMono
  /-- A fundamental sequence for `x` has limit `x` -/
  exists_lt_of_lt : ∀ y < x, ∃ z ∈ s.range, y < z

theorem IsFundamental.isLimit {s : Sequence α} {x : α} (h : IsFunadmental s x) : IsLimit s

#exit
theorem isFundamental_of_isBot {x : α} (h : IsBot x) : IsFundamental ∅ x :=
  ⟨rfl, isLimit_of_isBot h⟩

theorem isFundamental_empty [OrderBot α] : IsFundamental ∅ (⊥ : α) :=
  isFundamental_of_isBot isBot_bot

theorem isFundamental_singleton {x y : α} (h : x ⋖ y) : IsFundamental {x} y :=
  ⟨rfl, isLimit_of_covBy h⟩

theorem isFundamental_succ_of_not_isMax [SuccOrder α] {x : α} (h : ¬ IsMax x) :
    IsFundamental {x} (succ x) :=
  isFundamental_singleton (covBy_succ_of_not_isMax h)

theorem isFundamental_succ [SuccOrder α] [NoMaxOrder α] (x : α) : IsFundamental {x} (succ x) :=
  isFundamental_succ_of_not_isMax (not_isMax x)

theorem IsFundamental.lt {s : Sequence α} {x y : α} (hx : x ∈ s) (h : IsFundamental s y) : x < y :=
  match s with
  | Sum.inl none => by contradiction
  | Sum.inl (some z) => by
    obtain rfl := hx
    exact (IsLimit.covBy h.isLimit).lt
  | Sum.inr f => by
    obtain ⟨n, rfl⟩ := hx
    exact (isLimit_ofFun.1 h.isLimit).2 ⟨n, le_rfl⟩

theorem IsFundamental.lt_apply {f : ℕ → α} {x : α} (h : IsFundamental (ofFun f) x) (n : ℕ) :
    f n < x :=
  h.lt (Set.mem_range_self n)

end LinearOrder

end Sequence

open Sequence

variable [LinearOrder α]

/-- A fundamental sequence system is a pi type of fundamental sequences, one for each element of the
order. -/
def FundamentalSystem (α : Type u) [LinearOrder α] : Type u :=
  ∀ top : α, { s : Sequence α // s.IsFundamental top }

example : FundamentalSystem ℕ
  | 0 => ⟨_, isFundamental_empty⟩
  | n + 1 => ⟨_, isFundamental_succ n⟩

/-- An auxiliary definition for `slowGrowing` and `fastGrowing`. The function `g` describes what
happens at the successor step. -/
private def growingAux (s : FundamentalSystem α) [WellFoundedLT α]
    (x : α) (g : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) : ℕ :=
  match s x with
  | ⟨Sum.inl none, _⟩ => n + 1
  | ⟨Sum.inl (some y), h⟩ => have := h.lt (mem_singleton y); g (growingAux s y g) n
  | ⟨Sum.inr f, h⟩ => have := h.lt (mem_range_setOf n); growingAux s (f n) g n
termination_by wellFounded_lt.wrap x

/-- The slow growing hierarchy, given a fundamental sequence system `s`, is defined as follows:
* `fastGrowing s ⊥ n = n + 1`
* `fastGrowing s (succ x) n = fastGrowing s x n + 1`
* `fastGrowing s x n = fastGrowing s (f n) n`, where `f` is the fundamental sequence converging to
  the limit `x`.
-/
def slowGrowing (s : FundamentalSystem α) [WellFoundedLT α] (x : α) : ℕ → ℕ :=
  growingAux s x fun f n ↦ f n + 1

/-- The fast growing hierarchy, given a fundamental sequence system `s`, is defined as follows:
* `fastGrowing s ⊥ n = n + 1`
* `fastGrowing s (succ x) n = (fastGrowing s x)^[n] n`
* `fastGrowing s x n = fastGrowing s (f n) n`, where `f` is the fundamental sequence converging to
  the limit `x`.
-/
def fastGrowing (s : FundamentalSystem α) [WellFoundedLT α] (x : α) : ℕ → ℕ :=
  growingAux s x fun f n ↦ f^[n] n

end Ordinal
