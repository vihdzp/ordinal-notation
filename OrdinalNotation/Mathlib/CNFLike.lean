import OrdinalNotation.Basic
import OrdinalNotation.Mathlib.Lemmas
import OrdinalNotation.Mathlib.List
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# CNF-like ordinal notations

We define the type `CNFLike` for ordinal notations built upon the Cantor Normal Form. The ultimate
objective is to implement all (most?) other ordinal notations in this repository in terms of it.
-/

universe u

open Ordinal Notation Set

section Lists
variable {E : Type u} {e e' : E} [LinearOrder E]

/-! ### Basic definitions -/

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
@[simp] theorem not_lt_zero (l : CNFList E) : ¬ l < 0 := List.not_lt_nil l.1

theorem isCNFList (l : CNFList E) : IsCNFList l.1 := l.2
@[simp] theorem zero_val : (0 : CNFList E).val = [] := rfl
@[simp] theorem one_val [Zero E] : (1 : CNFList E).val = [toLex (0, 1)] := rfl

/-- The predicate that `e` is bigger than the leading exponent in `l`. This is the condition on
which `⟨e, n⟩ :: l` can be a `CNFList`. -/
def expGT (e : E) (l : CNFList E) : Prop :=
  ∀ e' ∈ l.1.head?, (ofLex e').1 < e

@[simp] theorem expGT_zero (e : E) : expGT e 0 := by simp [expGT]
instance (e : E) (l) : Decidable (expGT e l) := inferInstanceAs (Decidable (∀ _, _))

theorem expGT.trans_le (h : expGT e l) (he : e ≤ e') : expGT e' l :=
  fun x hx ↦ (h x hx).trans_le he

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
theorem expGT_cons_iff {e₁ e₂ : E} {l : CNFList E} (h : expGT e₂ l) {n : ℕ+} :
    expGT e₁ (cons h n) ↔ e₂ < e₁ := by
  simp [expGT]

theorem cons_lt_cons_iff {e₁ e₂ : E} {l₁ l₂ : CNFList E}
    {h₁ : expGT e₁ l₁} {h₂ : expGT e₂ l₂} {n₁ n₂ : ℕ+} :
    cons h₁ n₁ < cons h₂ n₂ ↔ toLex (e₁, n₁) < toLex (e₂, n₂) ∨ e₁ = e₂ ∧ n₁ = n₂ ∧ l₁ < l₂ := by
  apply List.cons_lt_cons_iff.trans
  simp [and_assoc]

theorem cons_le_cons_iff {e₁ e₂ : E} {l₁ l₂ : CNFList E}
    {h₁ : expGT e₁ l₁} {h₂ : expGT e₂ l₂} {n₁ n₂ : ℕ+} :
    cons h₁ n₁ ≤ cons h₂ n₂ ↔ toLex (e₁, n₁) < toLex (e₂, n₂) ∨ e₁ = e₂ ∧ n₁ = n₂ ∧ l₁ ≤ l₂ := by
  apply List.cons_le_cons_iff.trans
  simp [and_assoc]

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

/-- The `CNFList` corresponding to `ω ^ e * n`. -/
def single (e : E) (n : ℕ+) : CNFList E :=
  cons (expGT_zero e) n

@[simp]
theorem val_single (e : E) (n : ℕ+) : (single e n).val = [toLex (e, n)] :=
  rfl

@[simp]
theorem expGT_single_iff {e₁ e₂ : E} {n : ℕ+} : expGT e₁ (single e₂ n) ↔ e₂ < e₁ :=
  expGT_cons_iff _

-- toLex → single is monotonic

/-! ### Notation instance -/

variable [Notation E]

private def reprAux (l : CNFList E) : Ordinal :=
  (l.1.map fun x ↦ ω ^ Notation.repr (ofLex x).1 * (ofLex x).2).sum

private theorem reprAux_cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    reprAux (cons h n) = ω ^ Notation.repr e * n + reprAux l :=
  rfl

private theorem le_reprAux_cons {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    ω ^ Notation.repr e ≤ reprAux (cons h n) :=
  le_add_of_le_left <| le_mul_of_one_le_right' (mod_cast n.one_le)

private theorem reprAux_lt' {l : CNFList E} {o : Ordinal}
    (h : ∀ x ∈ l.1.head?, Notation.repr (ofLex x).1 < o) :
    reprAux l < ω ^ o := by
  induction l using consRecOn with
  | zero => exact opow_pos _ omega0_pos
  | cons e' l he' n IH =>
    simp at h
    apply principal_add_omega0_opow
    · exact omega0_opow_mul_nat_lt h n
    · exact IH fun x hx ↦ (Notation.repr_strictMono (he' x hx)).trans h

private theorem expGT.reprAux_lt {l : CNFList E} (h : expGT e l) :
    reprAux l < ω ^ Notation.repr e :=
  reprAux_lt' (by simpa [expGT] using h)

private theorem expGT_iff_reprAux_lt {l : CNFList E} :
    expGT e l ↔ reprAux l < ω ^ Notation.repr e where
  mp := expGT.reprAux_lt
  mpr h := by
    induction l using consRecOn with
    | zero => exact expGT_zero e
    | cons e' l he' n IH =>
      rw [expGT_cons_iff]
      exact Notation.repr_lt_repr.1 <| (opow_lt_opow_iff_right one_lt_omega0).1 <|
        (le_reprAux_cons _ _).trans_lt h

private theorem reprAux_lt (l : CNFList E) : reprAux l < ω ^ Notation.top E :=
  reprAux_lt' fun _ _ ↦ Notation.repr_lt_top _

private theorem strictMono_reprAux : StrictMono (reprAux (E := E)) := by
  intro l m hlm
  induction m using consRecOn generalizing l with
  | zero => simp at hlm
  | cons e' m he' k IH' =>
    induction l using consRecOn with
    | zero =>
      apply (Ordinal.mul_pos _ _).trans_le (le_add_right _ _)
      · exact opow_pos _ omega0_pos
      · exact_mod_cast k.pos
    | cons e l he n IH =>
      simp_rw [reprAux_cons]
      obtain (h | ⟨rfl, rfl, h⟩) := cons_lt_cons_iff.1 hlm
      · calc
          _ < ω ^ Notation.repr e * (n + 1) := by
            rw [mul_add_one, add_lt_add_iff_left]
            exact he.reprAux_lt
          _ ≤ ω ^ Notation.repr e' * k := by
            obtain (h | ⟨rfl, h⟩) := Prod.Lex.toLex_lt_toLex.1 h
            · apply (lt_of_lt_of_le _ (le_mul_of_one_le_right' (mod_cast k.one_le))).le
              simpa [reprAux] using ((expGT_single_iff (n := n.1.succPNat)).2 h).reprAux_lt
            · exact mul_le_mul_left' (mod_cast h.nat_succ_le) _
          _ ≤ _ := le_self_add
      · simp_all

private theorem mem_range_reprAux_of_lt {o} (h : o < ω ^ Notation.top E) :
    o ∈ Set.range (reprAux (E := E)) := by
  induction o using CNFRec ω with
  | H0 => use 0; rfl
  | H o ho IH =>
    obtain ⟨e, he⟩ := Notation.mem_range_repr_iff_lt.2 <| (lt_opow_iff_log_lt one_lt_omega0 ho).1 h
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt o one_lt_omega0)
    obtain ⟨l, hl⟩ := IH ((mod_opow_log_lt_self ω ho).trans h)
    have h : expGT e l := by
      rw [expGT_iff_reprAux_lt, hl, ← he]
      apply mod_lt _ (opow_ne_zero _ omega0_ne_zero)
    refine ⟨cons h ⟨n, ?_⟩, ?_⟩
    · rw [← Nat.cast_lt (α := Ordinal), ← hn, Nat.cast_zero]
      exact div_opow_log_pos _ ho
    · rw [reprAux_cons, he, PNat.mk_coe, ← hn, hl, div_add_mod]

private theorem range_reprAux : Set.range (reprAux (E := E)) = Set.Iio (ω ^ Notation.top E) := by
  ext o
  refine ⟨?_, mem_range_reprAux_of_lt⟩
  rintro ⟨l, rfl⟩
  exact reprAux_lt l

/-- If `E` is an ordinal notation, then `CNFList E` is as well, by evaluating
`ω ^ e₀ * n₀ + ω ^ e₁ * n₁ + ⋯` in the obvious manner. -/
@[simps! repr_top]
noncomputable instance [Notation E] : Notation (CNFList E) where
  repr := ⟨(OrderEmbedding.ofStrictMono _ strictMono_reprAux).ltEmbedding, ω ^ Notation.top E,
    Set.ext_iff.1 range_reprAux⟩
  repr_zero := List.sum_nil
  repr_one := by simp [reprAux]

@[simp]
theorem repr_cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    Notation.repr (cons h n) = ω ^ Notation.repr e * n + Notation.repr l :=
  rfl

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
