import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.Interval.Set.Infinite
import OrdinalNotation.ForMathlib

universe u

open Order

namespace Ordinal

variable {α : Type u} {β : Type*}

/-! ### Sequences -/

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
instance : Singleton α (Sequence α) :=
  ⟨fun x ↦ Sum.inl (some x)⟩

/-- A sequence `ℕ → α`, whose limit is its supremum. -/
def ofFun (f : ℕ → α) : Sequence α :=
  Sum.inr f

@[simp]
theorem singleton_ne_empty (x : α) : ({x} : Sequence α) ≠ ∅ := by
  change Sum.inl _ ≠ Sum.inl _
  simp

@[simp]
theorem ofFun_ne_empty (f : ℕ → α) : ofFun f ≠ ∅ :=
  Sum.inr_ne_inl

@[simp] theorem empty_ne_singleton (x : α) : ∅ ≠ ({x} : Sequence α) := (singleton_ne_empty x).symm
@[simp] theorem empty_ne_ofFun (f : ℕ → α) : ∅ ≠ ofFun f := (ofFun_ne_empty f).symm

@[simp] theorem sum_inl_none_def : Sum.inl none = (∅ : Sequence α) := rfl
@[simp] theorem sum_inl_some_def (x : α) : Sum.inl (some x) = ({x} : Sequence α) := rfl
@[simp] theorem sum_inr_def (f : ℕ → α) : Sum.inr f = ofFun f := rfl

/-- Recursion on sequences, using the preferred forms of the constructors. -/
def recOn {p : Sequence α → Sort*} (s : Sequence α) (empty : p ∅) (singleton : ∀ x, p {x})
    (ofFun : ∀ f, p (ofFun f)) : p s :=
  match s with
  | Sum.inl none => empty
  | Sum.inl (some x) => singleton x
  | Sum.inr f => ofFun f

/-- The range of a sequence is the set of values it contains -/
def range : Sequence α → Set α
  | Sum.inl none => ∅
  | Sum.inl (some x) => {x}
  | Sum.inr f => Set.range f

@[simp] theorem range_empty : range (∅ : Sequence α) = ∅ := rfl
@[simp] theorem range_singleton (x : α) : range {x} = {x} := rfl
@[simp] theorem range_ofFun (f : ℕ → α) : range (ofFun f) = Set.range f := rfl

/-- Membership predicate for sequences -/
def mem (s : Sequence α) (x : α) : Prop :=
  x ∈ s.range

instance : Membership α (Sequence α) :=
  ⟨mem⟩

@[simp] theorem not_mem_empty (x : α) : x ∉ (∅ : Sequence α) := id
@[simp] theorem mem_singleton_iff {x y : α} : x ∈ ({y} : Sequence α) ↔ x = y := Iff.rfl
@[simp] theorem mem_ofFun_iff {x : α} {f : ℕ → α} : x ∈ ofFun f ↔ x ∈ Set.range f := Iff.rfl
@[simp] theorem mem_range_iff {s : Sequence α} {x : α} : x ∈ s.range ↔ x ∈ s := Iff.rfl

theorem mem_singleton (x : α) : x ∈ ({x} : Sequence α) := mem_singleton_iff.2 rfl
theorem mem_ofFun {f : ℕ → α} (n : ℕ) : f n ∈ ofFun f := ⟨n, rfl⟩

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
theorem map_eq_empty_iff {s : Sequence α} {g : α → β} : s.map g = ∅ ↔ s = ∅ := by
  apply s.recOn <;> simp

@[simp]
theorem mem_map {s : Sequence α} {f : α → β} {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
  match s with
  | Sum.inl none => by simp
  | Sum.inl (some x) => by simp [eq_comm]
  | Sum.inr g => by simp

/-- Attach to a sequence the proof that it contains all its elements -/
def attach : (s : Sequence α) → Sequence {a : α // a ∈ s}
  | Sum.inl none => ∅
  | Sum.inl (some x) => {⟨x, rfl⟩}
  | Sum.inr f => ofFun fun n ↦ ⟨f n, n, rfl⟩

@[simp] theorem attach_empty : (∅ : Sequence α).attach = ∅ := rfl
@[simp] theorem attach_singleton (x : α) : ({x} : Sequence α).attach = {⟨x, rfl⟩} := rfl
@[simp] theorem attach_ofFun (f : ℕ → α) : (ofFun f).attach = ofFun fun n ↦ ⟨f n, n, rfl⟩ := rfl

@[simp]
theorem attach_eq_empty_iff {s : Sequence α} : s.attach = ∅ ↔ s = ∅ := by
  apply s.recOn <;> simp

@[simp]
theorem mem_attach {s : Sequence α} {x : α} : ∀ h : x ∈ s, ⟨x, h⟩ ∈ s.attach := by
  apply s.recOn <;> simp

/-- Partial map -/
def pmap (s : Sequence α) (f : ∀ x ∈ s, β) : Sequence β :=
  s.attach.map fun x ↦ f x.1 x.2

@[simp]
theorem pmap_empty (f : ∀ x ∈ (∅ : Sequence α), β) : pmap ∅ f = ∅ :=
  rfl

/-- `pmap_empty` but avoids type rewrites -/
theorem pmap_eq_empty_of_empty {s : Sequence α} (hs : s = ∅)
    (f : ∀ x ∈ s, β) : Sequence.pmap s f = ∅ := by
  subst hs
  rfl

@[simp]
theorem pmap_singleton (y : α) (f : ∀ x ∈ ({y} : Sequence α), β) : pmap _ f = {f y rfl} :=
  rfl

@[simp]
theorem pmap_ofFun (g : ℕ → α) (f : ∀ x ∈ ofFun g, β) :
    pmap _ f = ofFun fun n ↦ f (g n) (Set.mem_range_self _) :=
  rfl

@[simp]
theorem pmap_eq_empty_iff {s : Sequence α} : {f : ∀ x ∈ s, β} → pmap _ f = ∅ ↔ s = ∅ := by
  apply s.recOn <;> simp

@[simp]
theorem mem_pmap {s : Sequence α} {f : ∀ x ∈ s, β} :
    b ∈ s.pmap f ↔ ∃ (a : α) (h : a ∈ s), f a h = b := by
  simp [pmap]

/-- Builds a list with the first `n` elements of the sequence. This can be used to print the
sequence. -/
def toList (s : Sequence α) (n : ℕ) : List α :=
  match s with
  | Sum.inl none => []
  | Sum.inl (some x) => [x]
  | Sum.inr f => (List.range n).map f

/-! ### Fundamental sequences -/

section Preorder

variable [Preorder α] [Preorder β]

/-- A sequence of length `0` or `1` is always strictly monotonic. For a sequence of length `ω`,
`StrictMono` just reduces to the usual predicate. -/
protected def StrictMono : Sequence α → Prop
  | Sum.inl _ => true
  | Sum.inr f => _root_.StrictMono f

@[simp] theorem strictMono_empty : (∅ : Sequence α).StrictMono := rfl
@[simp] theorem strictMono_singleton (x : α) : ({x} : Sequence α).StrictMono := rfl
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

end Preorder

section LinearOrder

variable [LinearOrder α] [LinearOrder β]

/-- The limit of a sequence is the least value strictly greater than all its elements.

A length 0 sequence converges at a minimal element. A length 1 sequence `x` converges at the
successor of `x`. -/
def IsLimit (s : Sequence α) (y : α) : Prop :=
  ∀ {x}, x < y ↔ ∃ z ∈ s, x ≤ z

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

theorem IsLimit.lt {s : Sequence α} {x y : α} : IsLimit s y → x ∈ s → x < y := by
  apply s.recOn
  · rintro _ ⟨⟩
  · rintro x h rfl
    exact (IsLimit.covBy h).lt
  · rintro x h ⟨n, rfl⟩
    exact (isLimit_ofFun.1 h).2 ⟨n, le_rfl⟩

/-- The only sequence converging to `⊥` is `∅` -/
theorem IsLimit.eq_empty [OrderBot α] {s : Sequence α} : IsLimit s ⊥ → s = ∅ := by
  apply s.recOn
  · simp
  · intro x h
    cases (h.lt (mem_singleton _)).ne_bot rfl
  · intro x h
    cases (h.lt (mem_ofFun 0)).ne_bot rfl

@[simp]
theorem IsLimit.bot_iff_eq_empty [OrderBot α] {s : Sequence α} : IsLimit s ⊥ ↔ s = ∅ := by
  use IsLimit.eq_empty
  rintro rfl
  exact isLimit_bot

/-- A fundamental sequence for `x` is a strictly monotonic sequence with limit `x`. -/
@[mk_iff]
structure IsFundamental (s : Sequence α) (x : α) : Prop where
  /-- A fundamental sequence is strictly monotonic -/
  strictMono : s.StrictMono
  /-- A fundamental sequence for `x` has limit `x` -/
  isLimit : IsLimit s x

@[simp]
theorem isFundamental_empty {x : α} : IsFundamental ∅ x ↔ IsBot x := by
  simp [isFundamental_iff]

alias ⟨IsFundamental.isBot, isFundamental_of_isBot⟩ := isFundamental_empty

theorem isFundamental_bot [OrderBot α] : IsFundamental ∅ (⊥ : α) :=
  isFundamental_of_isBot isBot_bot

@[simp]
theorem isFundamental_singleton {x y : α} : IsFundamental {x} y ↔ x ⋖ y := by
  simp [isFundamental_iff, covBy_iff_lt_iff_le]

alias ⟨IsFundamental.covBy, isFundamental_of_covBy⟩ := isFundamental_singleton

theorem isFundamental_succ_of_not_isMax [SuccOrder α] {x : α} (h : ¬ IsMax x) :
    IsFundamental {x} (succ x) :=
  isFundamental_of_covBy (covBy_succ_of_not_isMax h)

theorem isFundamental_succ [SuccOrder α] [NoMaxOrder α] (x : α) : IsFundamental {x} (succ x) :=
  isFundamental_succ_of_not_isMax (not_isMax x)

theorem IsFundamental.lt {s : Sequence α} {x y : α} (hx : x ∈ s) (h : IsFundamental s y) : x < y :=
  IsLimit.lt h.isLimit hx

/-- The only fundamental sequence for `⊥` is `∅` -/
theorem IsFundamental.eq_empty [OrderBot α] {s : Sequence α} : IsFundamental s ⊥ → s = ∅ :=
  fun h ↦ IsLimit.eq_empty h.isLimit

@[simp]
theorem IsFundamental.bot_iff_eq_empty [OrderBot α] {s : Sequence α} :
    IsFundamental s ⊥ ↔ s = ∅ := by
  use IsFundamental.eq_empty
  rintro rfl
  exact isFundamental_bot

theorem IsFundamental.isSuccLimit {f : ℕ → α} {x : α} (h : IsFundamental (ofFun f) x) :
    IsSuccLimit x := by
  use not_isMin_of_lt (h.lt (mem_ofFun 0))
  intro y hx
  obtain ⟨z, ⟨n, rfl⟩, hy⟩ := h.2.1 hx.lt
  exact (hx.ge_of_gt <| hy.trans_lt (h.1 (Nat.lt_succ_self _))).not_lt (h.lt (mem_ofFun _))

/-- The only fundamental sequence for `succ x` is `{x}` -/
theorem IsFundamental.eq_succ [SuccOrder α] [NoMaxOrder α] {s : Sequence α} :
    IsFundamental s (succ x) → s = {x} := by
  have : Inhabited α := ⟨x⟩
  have : Infinite α := NoMaxOrder.infinite
  apply s.recOn
  · simp
  · simp [← succ_eq_iff_covBy]
  · intro f hf
    simpa using hf.isSuccLimit

@[simp]
theorem IsFundamental.succ_iff_eq_singleton [SuccOrder α] [NoMaxOrder α] {s : Sequence α} :
    IsFundamental s (succ x) ↔ s = {x} := by
  use IsFundamental.eq_succ
  rintro rfl
  exact isFundamental_succ x

end LinearOrder

end Sequence

open Sequence

variable [LinearOrder α]

/-- A fundamental sequence system is a pi type of fundamental sequences, one for each element of the
order. -/
def FundamentalSystem (α : Type u) [LinearOrder α] : Type u :=
  ∀ x : α, { s : Sequence α // s.IsFundamental x }

example : FundamentalSystem ℕ
  | 0 => ⟨_, isFundamental_bot⟩
  | n + 1 => ⟨_, isFundamental_succ n⟩

theorem fundamentalSystem_bot [OrderBot α] (s : FundamentalSystem α) :
    s ⊥ = ⟨∅, isFundamental_bot⟩ :=
  Subtype.ext (s ⊥).2.eq_empty

theorem fundamentalSystem_succ [SuccOrder α] [NoMaxOrder α] (s : FundamentalSystem α) (x : α) :
    s (succ x) = ⟨_, isFundamental_succ x⟩ :=
  Subtype.ext (s _).2.eq_succ

/-! ### Fast growing hierarchy -/

/-- An auxiliary definition for `slowGrowing` and `fastGrowing`. The function `g` describes what
happens at the successor step. -/
private def growingAux (s : FundamentalSystem α) [WellFoundedLT α]
    (x : α) (g : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) : ℕ :=
  match s x with
  | ⟨Sum.inl none, _⟩ => n + 1
  | ⟨Sum.inl (some y), h⟩ => have := h.lt (mem_singleton y); g (growingAux s y g) n
  | ⟨Sum.inr f, h⟩ => have := h.lt (mem_ofFun n); growingAux s (f n) g n
termination_by wellFounded_lt.wrap x

variable [WellFoundedLT α]

private theorem growingAux_bot [OrderBot α] (s : FundamentalSystem α)
    (g : (ℕ → ℕ) → ℕ → ℕ) : growingAux s ⊥ g = Nat.succ := by
  ext n
  rw [growingAux, fundamentalSystem_bot s]

private theorem growingAux_succ [SuccOrder α] [NoMaxOrder α] (s : FundamentalSystem α) (x : α)
    (g : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) : growingAux s (succ x) g n = g (growingAux s x g) n := by
  rw [growingAux, fundamentalSystem_succ s]

private theorem growingAux_limit (s : FundamentalSystem α) {x : α} {f : ℕ → α} (h : s x = ofFun f)
    (g : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) : growingAux s x g n = growingAux s (f n) g n := by
  have : s x = ⟨ofFun f, h ▸ (s x).2⟩ := Subtype.eq h
  rw [growingAux, this]
  rfl

/-- The slow growing hierarchy, given a fundamental sequence system `s`, is defined as follows:
* `fastGrowing s ⊥ n = n + 1`
* `fastGrowing s (succ x) n = fastGrowing s x n + 1`
* `fastGrowing s x n = fastGrowing s (f n) n`, where `f` is the fundamental sequence converging to
  the limit `x`.
-/
def slowGrowing (s : FundamentalSystem α) (x : α) : ℕ → ℕ :=
  growingAux s x fun f n ↦ f n + 1

/-- The unapplied version of `slowGrowing_bot` -/
@[simp]
theorem slowGrowing_bot' [OrderBot α] (s : FundamentalSystem α) :
    slowGrowing s ⊥ = Nat.succ :=
  growingAux_bot ..

theorem slowGrowing_bot [OrderBot α] (s : FundamentalSystem α) (n : ℕ) :
    slowGrowing s ⊥ n = n + 1 := by
  rw [slowGrowing_bot']

@[simp]
theorem slowGrowing_succ [SuccOrder α] [NoMaxOrder α] (s : FundamentalSystem α) (x : α) (n : ℕ) :
    slowGrowing s (succ x) n = slowGrowing s x n + 1 :=
  growingAux_succ ..

theorem slowGrowing_limit (s : FundamentalSystem α) {x : α} {f : ℕ → α} (h : s x = ofFun f)
    (n : ℕ) : slowGrowing s x n = slowGrowing s (f n) n :=
  growingAux_limit s h ..

/-- The fast growing hierarchy, given a fundamental sequence system `s`, is defined as follows:
* `fastGrowing s ⊥ n = n + 1`
* `fastGrowing s (succ x) n = (fastGrowing s x)^[n] n`
* `fastGrowing s x n = fastGrowing s (f n) n`, where `f` is the fundamental sequence converging to
  the limit `x`.
-/
def fastGrowing (s : FundamentalSystem α) [WellFoundedLT α] (x : α) : ℕ → ℕ :=
  growingAux s x fun f n ↦ f^[n] n

/-- The unapplied version of `fastGrowing_bot` -/
@[simp]
theorem fastGrowing_bot' [OrderBot α] (s : FundamentalSystem α) :
    fastGrowing s ⊥ = Nat.succ :=
  growingAux_bot ..

theorem fastGrowing_bot [OrderBot α] (s : FundamentalSystem α) (n : ℕ) :
    fastGrowing s ⊥ n = n + 1 := by
  rw [fastGrowing_bot']

@[simp]
theorem fastGrowing_succ [SuccOrder α] [NoMaxOrder α] (s : FundamentalSystem α) (x : α) (n : ℕ) :
    fastGrowing s (succ x) n = (fastGrowing s x)^[n] n :=
  growingAux_succ ..

theorem fastGrowing_limit (s : FundamentalSystem α) {x : α} {f : ℕ → α} (h : s x = ofFun f)
    (n : ℕ) : fastGrowing s x n = fastGrowing s (f n) n :=
  growingAux_limit s h ..

end Ordinal
