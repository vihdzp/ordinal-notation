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

variable {s : Sequence α} {x y : α} {f : ℕ → α}

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

@[simp] theorem ofFun_ne_empty (f : ℕ → α) : ofFun f ≠ ∅ := Sum.inr_ne_inl
@[simp] theorem singleton_ne_ofFun (x : α) (f : ℕ → α) : {x} ≠ ofFun f := Sum.inl_ne_inr
@[simp] theorem empty_ne_singleton (x : α) : ∅ ≠ ({x} : Sequence α) := (singleton_ne_empty x).symm
@[simp] theorem empty_ne_ofFun (f : ℕ → α) : ∅ ≠ ofFun f := (ofFun_ne_empty f).symm
@[simp] theorem ofFun_ne_singleton (x : α) (f : ℕ → α) : ofFun f ≠ {x} := Sum.inr_ne_inl

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

/-- The length of a sequence as an element of `WithTop ℕ`. This can be used as a proxy for asking
what type of sequence we're dealing with.-/
def length : Sequence α → WithTop ℕ
  | Sum.inl none => 0
  | Sum.inl (some _) => 1
  | Sum.inr _ => ⊤

@[simp] theorem length_empty : (∅ : Sequence α).length = 0 := rfl
@[simp] theorem length_singleton (x : α) : ({x} : Sequence α).length = 1 := rfl
@[simp] theorem length_ofFun (f : ℕ → α) : (ofFun f).length = ⊤ := rfl

@[simp] theorem length_eq_zero_iff : s.length = 0 ↔ s = ∅ := by
  apply s.recOn <;> simp

theorem length_eq_one_iff : s.length = 1 ↔ ∃ x, s = {x} := by
  apply s.recOn <;> simp

theorem length_eq_top_iff : s.length = ⊤ ↔ ∃ f, s = ofFun f := by
  apply s.recOn <;> simp

/-- The range of a sequence is the set of values it attains -/
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
@[simp] theorem mem_singleton_iff : x ∈ ({y} : Sequence α) ↔ x = y := Iff.rfl
@[simp] theorem mem_ofFun_iff : x ∈ ofFun f ↔ x ∈ Set.range f := Iff.rfl
@[simp] theorem mem_range_iff : x ∈ s.range ↔ x ∈ s := Iff.rfl

theorem mem_singleton (x : α) : x ∈ ({x} : Sequence α) := mem_singleton_iff.2 rfl
theorem mem_ofFun (n : ℕ) : f n ∈ ofFun f := ⟨n, rfl⟩

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
theorem map_length (s : Sequence α) (g : α → β) : (s.map g).length = s.length := by
  apply s.recOn <;> simp

@[simp]
theorem map_eq_empty_iff : s.map g = ∅ ↔ s = ∅ := by
  apply s.recOn <;> simp

@[simp]
theorem mem_map {b : β} {g : α → β} : b ∈ s.map g ↔ ∃ a ∈ s, g a = b :=
  match s with
  | Sum.inl none | Sum.inr f => by simp
  | Sum.inl (some x) => by simp [eq_comm]

/-- Attach to a sequence the proof that it contains all its elements -/
def attach : (s : Sequence α) → Sequence {a : α // a ∈ s}
  | Sum.inl none => ∅
  | Sum.inl (some x) => {⟨x, rfl⟩}
  | Sum.inr f => ofFun fun n ↦ ⟨f n, n, rfl⟩

@[simp] theorem attach_empty : (∅ : Sequence α).attach = ∅ := rfl
@[simp] theorem attach_singleton (x : α) : ({x} : Sequence α).attach = {⟨x, rfl⟩} := rfl
@[simp] theorem attach_ofFun (f : ℕ → α) : (ofFun f).attach = ofFun fun n ↦ ⟨f n, n, rfl⟩ := rfl

@[simp]
theorem attach_length (s : Sequence α) : s.attach.length = s.length := by
  apply s.recOn <;> simp

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
theorem pmap_length (s : Sequence α) (f : ∀ x ∈ s, β) : (pmap s f).length = s.length := by
  simp [pmap]

@[simp]
theorem pmap_eq_empty_iff {s : Sequence α} : {f : ∀ x ∈ s, β} → pmap _ f = ∅ ↔ s = ∅ := by
  apply s.recOn <;> simp

@[simp]
theorem mem_pmap {b : β} {f : ∀ x ∈ s, β} :
    b ∈ s.pmap f ↔ ∃ (a : α) (h : a ∈ s), f a h = b := by
  simp [pmap]

/-- `s.add x` is the map of `s` through `x + ·`.

Under reasonable typeclass assumptions for an ordinal notation, `s.add x` will be a fundamental
sequence for `x + y` whenever `s` is a fundamental sequence for `y`. -/
def add [Add α] (s : Sequence α) (x : α) : Sequence α :=
  s.map (x + ·)

@[simp] theorem add_empty [Add α] (x : α) : (∅ : Sequence α).add x = ∅ := rfl
@[simp] theorem add_singleton [Add α] (x y : α) : ({x} : Sequence α).add y = {y + x} := rfl
@[simp] theorem add_ofFun [Add α] (f : ℕ → α) (x : α) :
    (ofFun f).add x = ofFun fun y ↦ x + f y := rfl

@[simp]
theorem add_length [Add α] (s : Sequence α) (x : α) : (s.add x).length = s.length :=
  map_length _ _

/-- `s[n]` returns the `n`-th element of the fundamental sequence `s`, as an element of `WithBot α`.
By convention, we take `∅[n] = ⊥` and `{x}[n] = x`. This ensures various convenient properties such
as `getElem` being an injection, or `(s.add x)[n] = x + s[n]` -/
instance : GetElem (Sequence α) ℕ (WithBot α) fun _ _ ↦ True
  where getElem s n _ := match s with
    | Sum.inl none => ⊥
    | Sum.inl (some x) => x
    | Sum.inr f => f n

@[simp] theorem getElem_empty (n : ℕ) : (∅ : Sequence α)[n] = ⊥ := rfl
@[simp] theorem getElem_singleton (x : α) (n : ℕ) : ({x} : Sequence α)[n] = x := rfl
@[simp] theorem getElem_ofFun (f : ℕ → α) (n : ℕ) : (ofFun f)[n] = f n := rfl

@[simp]
theorem getElem_add [Add α] (s : Sequence α) (x : α) (n : ℕ) : (s.add x)[n] = x + s[n] := by
  apply s.recOn <;> simp

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

/-- A sequence of length 0 or 1 is always strictly monotonic. For a sequence of length `ω`,
`StrictMono` just reduces to the usual predicate. -/
protected def StrictMono : Sequence α → Prop
  | Sum.inl _ => True
  | Sum.inr f => _root_.StrictMono f

@[simp] theorem strictMono_empty : (∅ : Sequence α).StrictMono := ⟨⟩
@[simp] theorem strictMono_singleton (x : α) : ({x} : Sequence α).StrictMono := ⟨⟩
@[simp] theorem strictMono_ofFun : (ofFun f).StrictMono ↔ StrictMono f := Iff.rfl

theorem StrictMono.map (hs : s.StrictMono) {g : α → β} (h : StrictMono g) :
    (s.map g).StrictMono :=
  match s with
  | Sum.inl none | Sum.inl (some _) => ⟨⟩
  | Sum.inr _ => h.comp hs

theorem StrictMono.attach (hs : s.StrictMono) : s.attach.StrictMono :=
  match s with
  | Sum.inl none | Sum.inl (some _) => ⟨⟩
  | Sum.inr _ => fun _ _ h ↦ hs h

end Preorder

section LinearOrder

variable [LinearOrder α] [LinearOrder β]

/-- The limit of a sequence is the least value strictly greater than all its elements.

A length 0 sequence converges at a minimal element. A length 1 sequence `x` converges at
`succ x`. -/
def IsLimit (s : Sequence α) (y : α) : Prop :=
  ∀ {x}, x < y ↔ ∃ z ∈ s, x ≤ z

theorem IsLimit.exists_le_of_lt (hl : IsLimit s y) (h : x < y) :
    ∃ z ∈ s, x ≤ z :=
  hl.1 h

theorem IsLimit.lt (hl : IsLimit s y) (h : x ∈ s) : x < y :=
  hl.2 ⟨x, h, le_rfl⟩

@[simp]
theorem isLimit_empty : IsLimit ∅ x ↔ IsMin x := by
  simp [IsLimit, isMin_iff_forall_not_lt]

alias ⟨IsLimit.isMin, isLimit_of_isMin⟩ := isLimit_empty

theorem isLimit_bot [OrderBot α] : IsLimit ∅ (⊥ : α) :=
  isLimit_of_isMin isMin_bot

@[simp]
theorem isLimit_singleton : IsLimit {x} y ↔ x ⋖ y := by
  simp [IsLimit, covBy_iff_lt_iff_le]

alias ⟨IsLimit.covBy, isLimit_of_covBy⟩ := isLimit_singleton

theorem isLimit_succ_of_not_isMax [SuccOrder α] (h : ¬ IsMax x) : IsLimit {x} (succ x) :=
  isLimit_of_covBy (covBy_succ_of_not_isMax h)

theorem isLimit_succ [SuccOrder α] [NoMaxOrder α] (x : α) : IsLimit {x} (succ x) :=
  isLimit_succ_of_not_isMax (not_isMax x)

theorem isLimit_ofFun : IsLimit (ofFun f) y ↔ ∀ {x}, x < y ↔ ∃ n, x ≤ f n := by
  simp [IsLimit]

/-- The only sequence converging to `⊥` is `∅` -/
theorem IsLimit.eq_empty [OrderBot α] : IsLimit s ⊥ → s = ∅ := by
  apply s.recOn
  · simp
  · intro x h
    cases (h.lt (mem_singleton x)).ne_bot rfl
  · intro x h
    cases (h.lt (mem_ofFun 0)).ne_bot rfl

@[simp]
theorem IsLimit.bot_iff_eq_empty [OrderBot α] : IsLimit s ⊥ ↔ s = ∅ := by
  use IsLimit.eq_empty
  rintro rfl
  exact isLimit_bot

theorem IsLimit.map (h : IsLimit s x) (f : α ≤i β) : IsLimit (s.map f) (f x) := by
  intro y
  simp_rw [mem_map, exists_exists_and_eq_and]
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := f.mem_range_of_le hy.le
    obtain ⟨z, hz, hyz⟩ := h.1 (f.lt_iff_lt.1 hy)
    exact ⟨z, hz, f.le_iff_le.2 hyz⟩
  · rintro ⟨z, hz, hyz⟩
    exact hyz.trans_lt (f.lt_iff_lt.2 <| h.lt hz)

private theorem isLimit_congr' (hx : IsLimit s x) (hy : IsLimit s y) :
    x ≤ y := by
  apply le_of_not_lt fun h ↦ ?_
  obtain ⟨z, hz, hyz⟩ := hx.1 h
  exact hyz.not_lt (hy.lt hz)

/-- A sequence has at most one limit. -/
theorem isLimit_congr (hx : IsLimit s x) (hy : IsLimit s y) : x = y :=
  (isLimit_congr' hx hy).antisymm (isLimit_congr' hy hx)

/-- A fundamental sequence for `x` is a strictly monotonic sequence with limit `x`. -/
@[mk_iff]
structure IsFundamental (s : Sequence α) (x : α) : Prop where
  /-- A fundamental sequence is strictly monotonic -/
  strictMono : s.StrictMono
  /-- A fundamental sequence for `x` has limit `x` -/
  isLimit : IsLimit s x

@[simp]
theorem isFundamental_empty : IsFundamental ∅ x ↔ IsMin x := by
  simp [isFundamental_iff]

alias ⟨IsFundamental.isMin, isFundamental_of_isMin⟩ := isFundamental_empty

theorem isFundamental_bot [OrderBot α] : IsFundamental ∅ (⊥ : α) :=
  isFundamental_of_isMin isMin_bot

@[simp]
theorem isFundamental_singleton : IsFundamental {x} y ↔ x ⋖ y := by
  simp [isFundamental_iff, covBy_iff_lt_iff_le]

alias ⟨IsFundamental.covBy, isFundamental_of_covBy⟩ := isFundamental_singleton

theorem isFundamental_succ_of_not_isMax [SuccOrder α] (h : ¬ IsMax x) :
    IsFundamental {x} (succ x) :=
  isFundamental_of_covBy (covBy_succ_of_not_isMax h)

theorem isFundamental_succ [SuccOrder α] [NoMaxOrder α] (x : α) : IsFundamental {x} (succ x) :=
  isFundamental_succ_of_not_isMax (not_isMax x)

theorem IsFundamental.lt (hx : x ∈ s) (h : IsFundamental s y) : x < y :=
  IsLimit.lt h.isLimit hx

/-- The only fundamental sequence for `⊥` is `∅` -/
theorem IsFundamental.eq_empty [OrderBot α] : IsFundamental s ⊥ → s = ∅ :=
  fun h ↦ IsLimit.eq_empty h.isLimit

@[simp]
theorem IsFundamental.bot_iff_eq_empty [OrderBot α] : IsFundamental s ⊥ ↔ s = ∅ := by
  use IsFundamental.eq_empty
  rintro rfl
  exact isFundamental_bot

theorem IsFundamental.isSuccLimit (h : IsFundamental (ofFun f) x) : IsSuccLimit x := by
  use not_isMin_of_lt (h.lt (mem_ofFun 0))
  intro y hx
  obtain ⟨z, ⟨n, rfl⟩, hy⟩ := h.2.1 hx.lt
  exact (hx.ge_of_gt <| hy.trans_lt (h.1 (Nat.lt_succ_self _))).not_lt (h.lt (mem_ofFun _))

theorem IsFundamental.isSuccLimit_iff : IsFundamental s x →
    (IsSuccLimit x ↔ s.length = ⊤) := by
  apply s.recOn
  · simpa using fun hx h ↦ h.1 hx
  · simpa using fun y hy h ↦ h.2 y hy
  · simpa using fun f h ↦ h.isSuccLimit

theorem IsFundamental.isSuccPrelimit_iff : IsFundamental s x →
    (IsSuccPrelimit x ↔ s.length ≠ 1) := by
  apply s.recOn
  · simpa using fun h ↦ h.isSuccPrelimit
  · simpa using fun y hy h ↦ h y hy
  · simpa using fun f h ↦ h.isSuccLimit.isSuccPrelimit

/-- The only fundamental sequence for `succ x` is `{x}` -/
theorem IsFundamental.eq_succ [SuccOrder α] [NoMaxOrder α] :
    IsFundamental s (succ x) → s = {x} := by
  have : Inhabited α := ⟨x⟩
  have : Infinite α := NoMaxOrder.infinite
  apply s.recOn
  · simpa using not_isMin_succ x
  · simp [← succ_eq_iff_covBy]
  · intro f hf
    simpa using hf.isSuccLimit

@[simp]
theorem IsFundamental.succ_iff_eq_singleton [SuccOrder α] [NoMaxOrder α] :
    IsFundamental s (succ x) ↔ s = {x} := by
  use IsFundamental.eq_succ
  rintro rfl
  exact isFundamental_succ x

theorem IsFundamental.map (h : IsFundamental s x) (f : α ≤i β) : IsFundamental (s.map f) (f x) :=
  ⟨h.1.map f.strictMono, IsLimit.map h.2 _⟩

/-- A sequence is fundamental for at most one value. -/
theorem isFundamental_congr (hx : IsFundamental s x) (hy : IsFundamental s y) : x = y :=
  isLimit_congr hx.2 hy.2

end LinearOrder

end Sequence

open Sequence

variable [LinearOrder α]

/-- A typeclass for types with a "canonical" system of fundamental sequences. -/
class FundamentalSystem (α : Type u) [LinearOrder α] where
  /-- Returns a fundamental sequence for each element of the type. -/
  fundamentalSeq : α → Sequence α
  /-- The fundamental sequence for `x` has the necessary property. -/
  isFundamental_fundamentalSeq (x : α) : IsFundamental (fundamentalSeq x) x

/-- A "canonical" fundamental sequence for `x`. -/
def fundamentalSeq [FundamentalSystem α] (x : α) : Sequence α :=
  FundamentalSystem.fundamentalSeq x

theorem isFundamental_fundamentalSeq [FundamentalSystem α] (x : α) :
    IsFundamental (fundamentalSeq x) x :=
  FundamentalSystem.isFundamental_fundamentalSeq x

@[ext]
theorem FundamentalSystem.ext {s t : FundamentalSystem α}
    (h : ∀ x, s.fundamentalSeq x = t.fundamentalSeq x) : s = t := by
  cases s
  cases t
  congr
  ext
  exact h _

@[simp]
theorem fundamentalSeq_bot [FundamentalSystem α] [OrderBot α] :
    fundamentalSeq (⊥ : α) = ∅ :=
  (isFundamental_fundamentalSeq _).eq_empty

@[simp]
theorem fundamentalSeq_succ [FundamentalSystem α] [SuccOrder α] [NoMaxOrder α] (x : α) :
    fundamentalSeq (succ x) = {x} :=
  (isFundamental_fundamentalSeq _).eq_succ

@[simp]
theorem fundamentalSeq_add_one [FundamentalSystem α] [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    (x : α) : fundamentalSeq (x + 1) = {x} := by
  rw [← succ_eq_add_one]
  exact fundamentalSeq_succ x

theorem fundamentalSeq_injective [FundamentalSystem α] :
    Function.Injective (@fundamentalSeq α _ _) := by
  intro x y h
  exact isFundamental_congr (isFundamental_fundamentalSeq x) (h ▸ isFundamental_fundamentalSeq y)

@[simp]
theorem fundamentalSeq_inj [FundamentalSystem α] {x y : α}  :
    fundamentalSeq x = fundamentalSeq y ↔ x = y :=
  fundamentalSeq_injective.eq_iff

/-- Given a fundamental sequence system, one can decide if `x` is a successor limit by checking that
the length of its fundamental sequence is `ω`. -/
instance [FundamentalSystem α] : @DecidablePred α IsSuccLimit :=
  fun x ↦ decidable_of_iff' _ (isFundamental_fundamentalSeq x).isSuccLimit_iff

/-- Given a fundamental sequence system, one can decide if `x` is a successor pre-limit by checking
that the length of its fundamental sequence is not 1. -/
instance [FundamentalSystem α] : @DecidablePred α IsSuccPrelimit :=
  fun x ↦ decidable_of_iff' _ (isFundamental_fundamentalSeq x).isSuccPrelimit_iff

/-- The unique fundamental system on `ℕ`. The fast-growing hierarchy when endowed with this system
is sometimes called the Grzegorczyk hierarchy. -/
instance : FundamentalSystem ℕ where
  fundamentalSeq n := match n with
    | 0 => ∅
    | n + 1 => {n}
  isFundamental_fundamentalSeq n := match n with
    | 0 => isFundamental_bot
    | n + 1 => isFundamental_succ n

instance : Unique (FundamentalSystem ℕ) := by
  let s : FundamentalSystem ℕ := inferInstance
  refine ⟨⟨s⟩, fun _ ↦ ?_⟩
  ext n
  cases n
  · exact fundamentalSeq_bot.trans (@fundamentalSeq_bot _ _ s _).symm
  · exact (fundamentalSeq_succ _).trans (@fundamentalSeq_succ _ _ s _ _ _).symm

/-- Given a fundamental sequence system for `α`, extend it to a fundamental sequence system for
`WithTop α` by using a specified function as the fundamental sequence for `⊤`. -/
def FundamentalSystem.withTop [FundamentalSystem α] (f : ℕ → α) (hs : StrictMono f)
    (hl : ∀ x : α, ∃ n, x ≤ f n) : FundamentalSystem (WithTop α) where
  fundamentalSeq x := match x with
    | some x => (fundamentalSeq x).map some
    | ⊤ => ofFun (some ∘ f)
  isFundamental_fundamentalSeq x := match x with
    | some x => by
      let g : α ≤i WithTop α := @PrincipalSeg.withTopCoe α _
      exact (isFundamental_fundamentalSeq x).map g
    | ⊤ => by
      refine ⟨WithTop.coe_strictMono.comp hs, ⟨fun hx ↦ ?_, ?_⟩⟩
      · obtain ⟨x, rfl⟩ := PrincipalSeg.withTopCoe.mem_range_of_rel_top hx
        obtain ⟨n, hn⟩ := hl x
        exact ⟨_, mem_ofFun n, WithTop.coe_le_coe.2 hn⟩
      · simp_rw [mem_ofFun_iff, Set.mem_range, exists_exists_eq_and, forall_exists_index]
        exact fun n hn ↦ hn.trans_lt (WithTop.coe_lt_top _)

/-! ### Fast growing hierarchy -/

/-- An auxiliary definition for `slowGrowing` and `fastGrowing`. The function `g` describes what
happens at the successor step. -/
private def growingWith [FundamentalSystem α] [WellFoundedLT α] (x : α) (g : (ℕ → ℕ) → ℕ → ℕ)
    (n : ℕ) : ℕ :=
  let s : {s // IsFundamental s x} := ⟨_, isFundamental_fundamentalSeq x⟩
  match s with
  | ⟨Sum.inl none, _⟩ => n + 1
  | ⟨Sum.inl (some y), h⟩ => have := h.lt (mem_singleton y); g (growingWith y g) n
  | ⟨Sum.inr f, h⟩ => have := h.lt (mem_ofFun n); growingWith (f n) g n
termination_by wellFounded_lt.wrap x

variable [WellFoundedLT α] [FundamentalSystem α]

private theorem growingWith_bot [OrderBot α] (g : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) :
    growingWith (⊥ : α) g n = n + 1 := by
  unfold growingWith
  simp_rw [fundamentalSeq_bot]

private theorem growingWith_succ [SuccOrder α] [NoMaxOrder α] (x : α) (g : (ℕ → ℕ) → ℕ → ℕ) :
    growingWith (succ x) g n = g (growingWith x g) n := by
  unfold growingWith
  simp_rw [fundamentalSeq_succ]

private theorem growingWith_limit {x : α} {f : ℕ → α} (h : fundamentalSeq x = ofFun f)
    (g : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) : growingWith x g n = growingWith (f n) g n := by
  rw [growingWith]
  simp_rw [h]
  rfl

/-- The slow growing hierarchy, given a fundamental sequence system is defined as follows:
* `slowGrowing ⊥ n = n + 1`
* `slowGrowing (succ x) n = slowGrowing x n + 1`
* `slowGrowing x n = slowGrowing (f n) n`, where `f` is the fundamental sequence converging to the
  limit `x`.
-/
def slowGrowing (x : α) : ℕ → ℕ :=
  growingWith x fun f n ↦ f n + 1

theorem slowGrowing_bot_apply [OrderBot α] (n : ℕ) :
    slowGrowing (⊥ : α) n = n + 1 :=
  growingWith_bot ..

@[simp]
theorem slowGrowing_bot [OrderBot α] : slowGrowing (⊥ : α) = Nat.succ :=
  funext slowGrowing_bot_apply

@[simp]
theorem slowGrowing_succ [SuccOrder α] [NoMaxOrder α] (x : α) (n : ℕ) :
    slowGrowing (succ x) n = slowGrowing x n + 1 :=
  growingWith_succ ..

theorem slowGrowing_limit {x : α} {f : ℕ → α} (h : fundamentalSeq x = ofFun f) (n : ℕ) :
    slowGrowing x n = slowGrowing (f n) n :=
  growingWith_limit h ..

/-- The fast growing hierarchy, given a fundamental sequence system is defined as follows:
* `fastGrowing ⊥ n = n + 1`
* `fastGrowing (succ x) n = (fastGrowing x)^[n] n`
* `fastGrowing x n = fastGrowing (f n) n`, where `f` is the fundamental sequence converging to the
  limit `x`.
-/
def fastGrowing (x : α) : ℕ → ℕ :=
  growingWith x fun f n ↦ f^[n] n

theorem fastGrowing_bot_apply [OrderBot α] (n : ℕ) :
    fastGrowing (⊥ : α) n = n + 1 :=
  growingWith_bot ..

@[simp]
theorem fastGrowing_bot [OrderBot α] : fastGrowing (⊥ : α) = Nat.succ :=
  funext fastGrowing_bot_apply

theorem fastGrowing_succ_apply [SuccOrder α] [NoMaxOrder α] (x : α) (n : ℕ) :
    fastGrowing (succ x) n = (fastGrowing x)^[n] n :=
  growingWith_succ ..

@[simp]
theorem fastGrowing_succ [SuccOrder α] [NoMaxOrder α] (x : α) :
    fastGrowing (succ x) = fun n ↦ (fastGrowing x)^[n] n :=
  funext (fastGrowing_succ_apply x)

theorem fastGrowing_limit {x : α} {f : ℕ → α} (h : fundamentalSeq x = ofFun f)
    (n : ℕ) : fastGrowing x n = fastGrowing (f n) n :=
  growingWith_limit h ..

theorem fastGrowing_one [OrderBot α] [SuccOrder α] [NoMaxOrder α] :
    fastGrowing (succ (⊥ : α)) = fun n ↦ 2 * n := by
  simp [Nat.succ_iterate, two_mul]

theorem fastGrowing_one_apply [OrderBot α] [SuccOrder α] [NoMaxOrder α] (n : ℕ) :
    fastGrowing (succ (⊥ : α)) n = 2 * n :=
  congr_fun fastGrowing_one n

theorem fastGrowing_two [OrderBot α] [SuccOrder α] [NoMaxOrder α] :
    fastGrowing (succ (succ (⊥ : α))) = fun n ↦ 2 ^ n * n := by
  simp [Nat.succ_iterate, ← two_mul]

theorem fastGrowing_two_apply [OrderBot α] [SuccOrder α] [NoMaxOrder α] (n : ℕ) :
    fastGrowing (succ (succ (⊥ : α))) n = 2 ^ n * n :=
  congr_fun fastGrowing_two n

end Ordinal
