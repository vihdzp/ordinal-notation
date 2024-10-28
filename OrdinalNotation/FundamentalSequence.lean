import Mathlib.SetTheory.Ordinal.Arithmetic

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

/-- The range of a sequence is the set of values it contains -/
def range : Sequence α → Set α
  | Sum.inl none => ∅
  | Sum.inl (some x) => {x}
  | Sum.inr f => Set.range f

@[simp] theorem range_empty : range (∅ : Sequence α) = ∅ := rfl
@[simp] theorem range_singleton (x : α) : range ({x} : Sequence α) = {x} := rfl
@[simp] theorem range_ofFun (f : ℕ → α) : range (ofFun f) = Set.range f := rfl

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
structure FundamentalSeq (top : α) : Type u where
  /-- The underlying `Sequence` -/
  sequence : Sequence α
  /-- A fundamental sequence is strictly monotonic -/
  strictMono : sequence.StrictMono
  /-- The fundamental sequence converges at `top` -/
  isLimit : sequence.IsLimit top

namespace FundamentalSeq

@[ext]
theorem ext (top : α) {f g : FundamentalSeq top} (h : f.sequence = g.sequence) : f = g := by
  cases f; cases g;
  simpa

/-- Recursion on the possible sequences the fundamental sequence is made out of. -/
@[elab_as_elim]
def recOnSequence {top : α} {p : FundamentalSeq top → Sort*} (s : FundamentalSeq top)
    (empty : ∀ hl : IsMin top, p ⟨∅, rfl, hl⟩) (singleton : ∀ x (hl : x ⋖ top), p ⟨{x}, rfl, hl⟩)
    (ofNat : ∀ f (hs : StrictMono f) hl, p ⟨ofFun f, hs, hl⟩) : p s := by
  obtain ⟨(_ | _) | _, hs, hl⟩ := s
  · exact empty hl
  · exact singleton _ hl
  · exact ofNat _ hs hl

theorem lt_of_mem {top x : α} (s : FundamentalSeq top) : x ∈ s.sequence → x < top := by
  refine recOnSequence s ?_ ?_ ?_
  · simp
  · intro y hy
    rw [mem_singleton_iff]
    rintro rfl
    exact hy.lt
  · intro f hs hl hx
    obtain ⟨n, rfl⟩ := hx
    exact lt_of_strictMono_of_isLimit hs hl n

/-- Given a minimal element, the empty sequence is a fundamental sequence for it. -/
@[simps]
def ofIsMin {x : α} (hx : IsMin x) : FundamentalSeq x :=
  ⟨∅, strictMono_empty, isLimit_empty.2 hx⟩

/-- The empty sequence is a fundamental sequence for `⊥`. -/
abbrev bot [OrderBot α] : FundamentalSeq (⊥ : α) :=
  FundamentalSeq.ofIsMin isMin_bot

/-- The empty sequence is the only fundamental sequence for `⊥` -/
theorem eq_bot [OrderBot α] (s : FundamentalSeq (⊥ : α)) : s = bot := by
  ext
  refine recOnSequence s ?_ (fun x hx ↦ ?_) (fun f hs hl ↦ ?_)
  · simp
  · cases hx.lt.ne_bot rfl
  · cases (lt_of_strictMono_of_isLimit hs hl 0).ne_bot rfl

instance [OrderBot α] : Unique (FundamentalSeq (⊥ : α)) :=
  ⟨⟨bot⟩, eq_bot⟩

/-- If `y` covers `x`, then `x` is a fundamental sequence for `y`. -/
@[simps]
def ofCovby {x y : α} (h : x ⋖ y) : FundamentalSeq y :=
  ⟨_, strictMono_singleton x, Sequence.isLimit_ofElement.2 h⟩

/-- `x` is a fundamental sequence for `succ x`. -/
abbrev succ {x : α} (hx : ¬ IsMax x) [SuccOrder α] : FundamentalSeq (succ x) :=
  ofCovby (covBy_succ_of_not_isMax hx)

/-- In a linear order, if `y` covers `x` then the only fundamental sequence for `y` is `x`. -/
theorem eq_ofCovby {α} [LinearOrder α] {x y : α} (h : x ⋖ y)
    (s : FundamentalSeq y) : s = ofCovby h := by
  ext
  refine recOnSequence s (fun hl ↦ ?_) (fun z hz ↦ ?_) (fun f hf hl ↦ ?_)
  · cases hl.not_lt h.lt
  · obtain rfl := h.unique_left hz
    simp
  · obtain ⟨n, hn⟩ := hl.1 h.lt
    cases (hl.2 ⟨_, (h.ge_of_gt hn).trans_lt (hf n.lt_succ_self)⟩).false

/-- In a linear order, the only fundamental sequence for `succ x` is `x`. -/
theorem eq_succ {α} [LinearOrder α] [SuccOrder α] {x : α} (hx : ¬ IsMax x)
    (s : FundamentalSeq (Order.succ x)) : s = succ hx :=
  eq_ofCovby _ _

end FundamentalSeq

/-- A fundamental sequence system is a set of `FundamentalSeq`, one for each element of the
order. -/
def FundamentalSystem (α : Type u) [Preorder α] : Type u :=
  ∀ top : α, FundamentalSeq top

example : FundamentalSystem ℕ
  | 0 => FundamentalSeq.bot
  | n + 1 => FundamentalSeq.succ (not_isMax n)

/-- An auxiliary definition for `slowGrowing` and `fastGrowing`. The function `g` describes what
happens at the successor step. -/
private def growingAux (s : FundamentalSystem α) [WellFoundedLT α]
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
