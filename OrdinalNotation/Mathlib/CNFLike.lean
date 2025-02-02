import OrdinalNotation.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.Principal
import Init.Data.List

universe u

open Ordinal Set

section Lists
variable {E : Type u} [LinearOrder E]

/-- The property determining whether a list is a `CNFList`. -/
def IsCNFList (l : List (E ×ₗ ℕ+)) : Prop :=
  (l.map fun x ↦ (ofLex x).1).Sorted (· > ·)

namespace IsCNFList

@[simp] theorem nil : IsCNFList ([] : List (E ×ₗ ℕ+)) := List.sorted_nil
@[simp] theorem singleton (x : E ×ₗ ℕ+) : IsCNFList [x] := List.sorted_singleton _

theorem of_cons {x} {l : List (E ×ₗ ℕ+)} (h : IsCNFList (x :: l)) : IsCNFList l :=
  List.Sorted.of_cons h

theorem cons_cons {x y} {l : List (E ×ₗ ℕ+)} :
    IsCNFList (x :: y :: l) ↔ (ofLex y).1 < (ofLex x).1 ∧ IsCNFList (y :: l) :=
  List.sorted_cons_cons

end IsCNFList

/-- A list of exponents in `E` and coefficients in `ℕ+`, with the exponents in decreasing order.
This emulates a construction of the form `ω ^ e₀ * n₀ + ω ^ e₁ * n₁ + ⋯`, like the Cantor normal
form.

If `E` is an ordinal notation, then `CNFList` can also be given the structure of an ordinal
notation. Moreover, we can define arithmetic on this type through simpler arithmetic on `E`. -/
def CNFList (E : Type u) [LinearOrder E] : Type u :=
  Subtype (@IsCNFList E _)

namespace CNFList

instance : Zero (CNFList E) := ⟨⟨[], .nil⟩⟩
instance [Zero E] : One (CNFList E) := ⟨⟨[toLex (0, 1)], .singleton _⟩⟩
instance : LinearOrder (CNFList E) := Subtype.instLinearOrder _

@[simp] theorem zero_le (l : CNFList E) : 0 ≤ l := List.nil_le l.1
@[simp] theorem not_lt_zero (l : CNFList E) : ¬ l < 0 := l.not_lt_nil

theorem isCNFList (l : CNFList E) : IsCNFList l.1 := l.2
@[simp] theorem zero_val : (0 : CNFList E).val = [] := rfl
@[simp] theorem one_val [Zero E] : (1 : CNFList E).val = [toLex (0, 1)] := rfl

/-- The predicate that `e` is bigger than the leading exponent in `l`. This is the condition on
which `⟨e, n⟩ :: l` is a `CNFList`. -/
def expGT (e : E) (l : CNFList E) : Prop :=
  ∀ e' ∈ l.1.head?, (ofLex e').1 < e

@[simp] theorem expGT_zero (e : E) : expGT e 0 := by simp [expGT]
instance (e : E) (l) : Decidable (expGT e l) := inferInstanceAs (Decidable (∀ _, _))

theorem _root_.IsCNFList.expGT {x : E ×ₗ ℕ+} {l : List (E ×ₗ ℕ+)} (h : IsCNFList (x :: l)) :
    expGT (ofLex x).1 ⟨l, h.of_cons⟩ := by
  cases l with
  | nil => exact expGT_zero _
  | cons a l =>
    rw [IsCNFList.cons_cons] at h
    simpa [CNFList.expGT] using h.1

/-- Appends an item to a `CNFList`, given that the exponent is larger than the largest exponent of
the original list. -/
def cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) : CNFList E := by
  refine ⟨toLex (e, n) :: l.1, ?_⟩
  obtain ⟨_ | ⟨a, l⟩, hl⟩ := l
  · simp
  · rw [IsCNFList.cons_cons]
    exact ⟨h _ rfl, hl⟩

@[simp]
theorem val_cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    (cons h n).1 = toLex (e, n) :: l.1 :=
  rfl

@[simp]
theorem mk_cons_eq_cons {x : E ×ₗ ℕ+} {l : List (E ×ₗ ℕ+)} {h : IsCNFList (x :: l)} :
    ⟨x :: l, h⟩ = cons h.expGT x.2 :=
  rfl

@[simp]
theorem expGT_cons_iff {e₁ e₂ : E} {l : CNFList E} (h : expGT e₂ l) (n : ℕ+) :
    expGT e₁ (cons h n) ↔ e₂ < e₁ := by
  simp [expGT]

theorem cons_lt_cons_iff {e₁ e₂ : E} {l₁ l₂ : CNFList E}
    {h₁ : expGT e₁ l₁} {h₂ : expGT e₂ l₂} {n₁ n₂ : ℕ+} :
    cons h₁ n₁ < cons h₂ n₂ ↔ toLex (e₁, n₁) < toLex (e₂, n₂) ∨ e₁ = e₂ ∧ n₁ = n₂ ∧ l₁ < l₂ := by
  apply List.cons_lt_cons_iff.trans
  simp [and_assoc]

theorem cons_le_cons_iff {e₁ e₂ : E} {l₁ l₂ : CNFList E}
    {h₁ : expGT e₁ l₁} {h₂ : expGT e₂ l₂} {n₁ n₂ : ℕ+} :
    cons h₁ n₁ ≤ cons h₂ n₂ ↔ toLex (e₁, n₁) < toLex (e₂, n₂) ∨ toLex (e₁, n₁) = toLex (e₂, n₂) ∧ l₁ ≤ l₂ := by
  convert List.cons_le_cons_iff (a := toLex (e₁, n₁)) (b := toLex (e₂, n₂)) (l₁ := l₁.1) (l₂ := l₂.1)
  rw [cons, cons, Subtype.mk_le_mk]
  rfl

#exit
/-- A recursion principle on `CNFList.cons`. -/
@[elab_as_elim]
def consRecOn {p : CNFList E → Sort*} (l : CNFList E) (zero : p 0)
    (cons : ∀ e l (h : expGT e l) n, p l → p (cons h n)) : p l :=
  match l with
  | ⟨[], _⟩ => zero
  | ⟨x :: l, hl⟩ => cons _ _ hl.expGT x.2 (consRecOn ⟨l, hl.of_cons⟩ zero cons)
termination_by l.1

@[simp]
theorem consRecOn_zero {p : CNFList E → Sort*} (zero : p 0)
    (cons : ∀ e l (h : expGT e l) n, p l → p (cons h n)) : consRecOn 0 zero cons = zero :=
  by rw [consRecOn.eq_def]

@[simp]
theorem consRecOn_cons {p : CNFList E → Sort*} (zero : p 0)
    (cons : ∀ e l (h : expGT e l) n, p l → p (cons h n)) {e l} (h : expGT e l) (n : ℕ+) :
    consRecOn (.cons h n) zero cons = cons _ _ h n (consRecOn l zero cons) :=
  by rw [consRecOn.eq_def]; rfl

#exit

variable [Notation E]

private def reprAux (l : CNFList E) : Ordinal :=
  (l.1.map fun x ↦ ω ^ Notation.repr (ofLex x).1 * (ofLex x).2).sum

private theorem reprAux_zero : reprAux (E := E) 0 = 0 := rfl

private theorem reprAux_cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    reprAux (cons h n) = ω ^ Notation.repr e * n + reprAux l :=
  rfl

private theorem reprAux_lt {l : CNFList E} {b : Ordinal}
    (h : ∀ a ∈ l.1.head?, Notation.repr (ofLex a).1 < b) : reprAux l < ω ^ b := by
  induction l using consRecOn with
  | zero => exact opow_pos b omega0_pos
  | cons e l he n IH =>
    have hb : Notation.repr e < b := by simpa using h
    refine b.principal_add_omega0_opow (omega0_opow_mul_nat_lt hb _) (IH fun a ha ↦ ?_)
    obtain ⟨_ | ⟨c, l⟩, _⟩ := l
    · contradiction
    · rw [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      obtain rfl := ha
      rw [mk_cons_eq_cons, expGT_cons_iff] at he
      exact (Notation.repr_lt_repr.2 he).trans hb

theorem strictMono_reprAux : StrictMono (reprAux (E := E)) := by
  intro l m h
  induction m using consRecOn with
  | zero => simp at h
  | cons e' m he' k IH' =>
    induction l using consRecOn with
    | zero =>
      apply lt_of_lt_of_le (Ordinal.mul_pos _ _) (le_add_right _ _)
      · exact opow_pos _ omega0_pos
      · exact_mod_cast k.pos
    | cons e l he n IH =>
      simp [reprAux]

  /-induction l with
  | nil => exact opow_pos b omega0_pos
  | cons c l IH =>
    have hc : Notation.repr c.1 < b := by simpa using h
    refine b.principal_add_omega0_opow (omega0_opow_mul_nat_lt hc _) (IH (fun a ha ↦ ?_) H.of_cons)
    cases l with
    | nil => contradiction
    | cons d l =>
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      obtain rfl := ha
      rw [IsCNFList.cons_cons] at H
      exact (Notation.repr_lt_repr.2 H.1).trans hc-/

#exit


  #exit

noncomputable instance [Notation E] : Notation (CNFList E) where
  repr := by
    refine ⟨(OrderEmbedding.ofStrictMono (reprAux ∘ Subtype.val) ?_).ltEmbedding,
      ω ^ Notation.top E, ?_⟩
    · intro x y h
      sorry
    · sorry
  repr_zero := List.sum_nil
  repr_one := by simp [reprAux]

#exit
end CNFList

/-- A type which is order-isomorphic to `CNFList Exp` for some type of exponents. Arithmetic can be
transferred through this isomorphism. -/
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
