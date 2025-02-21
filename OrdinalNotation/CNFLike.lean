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

open Order Set

namespace Ordinal.Notation

variable {E : Type u} {e f : E}

/-! ### Basic definitions -/

/-- The property determining whether a list is a `CNFList`. -/
def IsCNFList [LinearOrder E] (l : List (E ×ₗ ℕ+)) : Prop :=
  (l.map fun x ↦ (ofLex x).1).Sorted (· > ·)

namespace IsCNFList
variable [LinearOrder E]

@[simp] theorem nil : IsCNFList ([] : List (E ×ₗ ℕ+)) := List.sorted_nil
@[simp] theorem singleton (x : E ×ₗ ℕ+) : IsCNFList [x] := List.sorted_singleton _

theorem of_cons {x} {l : List (E ×ₗ ℕ+)} (h : IsCNFList (x :: l)) : IsCNFList l :=
  List.Sorted.of_cons h

theorem cons_cons {x y} {l : List (E ×ₗ ℕ+)} :
    IsCNFList (x :: y :: l) ↔ (ofLex y).1 < (ofLex x).1 ∧ IsCNFList (y :: l) :=
  List.sorted_cons_cons

-- TODO: PR `List.Sorted.dropLast` to Mathlib.
theorem dropLast {l : List (E ×ₗ ℕ+)} (h : IsCNFList l) : IsCNFList l.dropLast := by
  match l with
  | [] | [a] | [a, b] => simp
  | a :: b :: c :: l =>
    rw [List.dropLast_cons₂, List.dropLast_cons₂, cons_cons, ← List.dropLast_cons₂]
    rw [cons_cons] at h
    exact ⟨h.1, h.2.dropLast⟩

end IsCNFList

/-- A list of exponents in `E` and coefficients in `ℕ+`, with the exponents in decreasing order.
This emulates a construction of the form `ω ^ e₀ * n₀ + ω ^ e₁ * n₁ + ⋯`, like the Cantor normal
form.

If `E` is an ordinal notation, then `CNFList` can also be given the structure of an ordinal
notation. Moreover, we can define arithmetic on this type through simpler arithmetic on `E`. -/
def CNFList (E : Type u) [LinearOrder E] : Type u :=
  Subtype (@IsCNFList E _)

namespace CNFList
section LinearOrder
variable [LinearOrder E]

@[ext] theorem ext {l m : CNFList E} : l.val = m.val → l = m := Subtype.ext

/-- The `CNFList` corresponding to `ω ^ e * n`. -/
def single (e : E) (n : ℕ+) : CNFList E :=
  ⟨[toLex (e, n)], .singleton _⟩

@[simp] theorem val_single (e : E) (n : ℕ+) : (single e n).val = [toLex (e, n)] := rfl

instance : Zero (CNFList E) := ⟨⟨[], .nil⟩⟩
instance [Zero E] : One (CNFList E) := ⟨single 0 1⟩
instance [One E] : Omega (CNFList E) := ⟨single 1 1⟩
instance : LinearOrder (CNFList E) := Subtype.instLinearOrder _

@[simp] theorem mk_nil : ⟨[], .nil⟩ = (0 : CNFList E) := rfl
@[simp] theorem zero_le (l : CNFList E) : 0 ≤ l := List.nil_le l.1
@[simp] theorem not_lt_zero (l : CNFList E) : ¬ l < 0 := List.not_lt_nil l.1

theorem isCNFList (l : CNFList E) : IsCNFList l.1 := l.2
@[simp] theorem val_zero : (0 : CNFList E).val = [] := rfl
@[simp] theorem val_one [Zero E] : (1 : CNFList E).val = [toLex (0, 1)] := rfl
@[simp] theorem val_omega [One E] : (omega : CNFList E).val = [toLex (1, 1)] := rfl
@[simp] theorem omega_def [One E] : single (1 : E) 1 = omega := rfl

/-- The cast from natural numbers is defined as `n = single 0 n`. -/
instance [Zero E] : NatCast (CNFList E) where
  natCast n := n.recOn 0 (fun n _ ↦ single 0 n.succPNat)

@[simp, norm_cast] theorem natCast_zero [Zero E] : (0 : ℕ) = (0 : CNFList E) := rfl
@[simp, norm_cast] theorem natCast_one [Zero E] : (1 : ℕ) = (1 : CNFList E) := rfl

@[simp] theorem val_pNat (n : ℕ+) [Zero E] : (n.val : CNFList E).1 = [toLex (0, n)] := by
  rw [← n.succPNat_natPred]; rfl

-- This works better with aesop.
theorem val_natCast (n : ℕ) [Zero E] : (n : CNFList E).1 =
    match n with | 0 => [] | s + 1 => [toLex (0, s.succPNat)] := by
  cases n <;> rfl

@[simp]
theorem single_zero [Zero E] (n : ℕ+) : single (0 : E) n = n.val := by
  rw [← n.succPNat_natPred]
  rfl

/-- The predicate that `e` is bigger than the leading exponent in `l` (if it exists). This is the
condition on which `⟨e, n⟩ :: l` can be a `CNFList`. -/
def expGT (e : E) (l : CNFList E) : Prop :=
  ∀ f ∈ l.1.head?, (ofLex f).1 < e

@[simp] theorem expGT_zero_right (e : E) : expGT e 0 := by simp [expGT]
instance (e : E) (l) : Decidable (expGT e l) := inferInstanceAs (Decidable (∀ _, _))

theorem expGT.trans_le (h : expGT e l) (he : e ≤ f) : expGT f l :=
  fun x hx ↦ (h x hx).trans_le he

theorem _root_.Ordinal.Notation.IsCNFList.expGT {x : E ×ₗ ℕ+} {l : List (E ×ₗ ℕ+)}
    (h : IsCNFList (x :: l)) : expGT (ofLex x).1 ⟨l, h.of_cons⟩ := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [IsCNFList.cons_cons] at h
    simpa [CNFList.expGT] using h.1

theorem expGT.isCNFList {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    IsCNFList (toLex (e, n) :: l.1) := by
  obtain ⟨_ | ⟨a, l⟩, hl⟩ := l
  · simp
  · rw [IsCNFList.cons_cons]
    exact ⟨h _ rfl, hl⟩

@[simp]
theorem expGT_single_iff {e₁ e₂ : E} {n : ℕ+} : expGT e₁ (single e₂ n) ↔ e₂ < e₁ := by
  simp [expGT]

/-- Appends an item `(e, n)` to a `CNFList`, given that the exponent is larger than the largest
exponent of the original list.

`cons e n l h` represents `ω ^ e * n + l`, and `h` is the proof that this construction is valid. -/
def cons (e : E) (n : ℕ+) (l : CNFList E) (h : expGT e l) : CNFList E :=
  ⟨toLex (e, n) :: l.1, h.isCNFList n⟩

@[simp]
theorem val_cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    (cons e n l h).1 = toLex (e, n) :: l.1 :=
  rfl

@[simp]
theorem mk_cons_eq_cons {x : E ×ₗ ℕ+} {l : List (E ×ₗ ℕ+)} {h : IsCNFList (x :: l)} :
    ⟨x :: l, h⟩ = cons _ (ofLex x).2 _ h.expGT :=
  rfl

@[simp] theorem cons_pos (hl : expGT e l) (n : ℕ+) : 0 < cons e n l hl := List.nil_lt_cons ..
@[simp] theorem cons_ne_zero (hl : expGT e l) (n : ℕ+) : cons e n l hl ≠ 0 := (cons_pos hl n).ne'
@[simp] theorem zero_ne_cons (hl : expGT e l) (n : ℕ+) : 0 ≠ cons e n l hl := (cons_pos hl n).ne
theorem single_eq_cons (e : E) (n : ℕ+) : single e n = cons e n 0 (expGT_zero_right e) := rfl

@[simp]
theorem expGT_cons_iff {e₁ e₂ : E} {l : CNFList E} (h : expGT e₂ l) {n : ℕ+} :
    expGT e₁ (cons e₂ n l h) ↔ e₂ < e₁ := by
  simp [expGT]

theorem cons_lt_cons_iff {e₁ e₂ : E} {l₁ l₂ : CNFList E}
    {h₁ : expGT e₁ l₁} {h₂ : expGT e₂ l₂} {n₁ n₂ : ℕ+} :
    cons e₁ n₁ l₁ h₁ < cons e₂ n₂ l₂ h₂ ↔
      toLex (e₁, n₁) < toLex (e₂, n₂) ∨ e₁ = e₂ ∧ n₁ = n₂ ∧ l₁ < l₂ := by
  apply List.cons_lt_cons_iff.trans
  simp [and_assoc]

theorem cons_lt_cons_fst {e₁ e₂ : E} {l₁ l₂ : CNFList E}
    {h₁ : expGT e₁ l₁} {h₂ : expGT e₂ l₂} {n₁ n₂ : ℕ+} (h : e₁ < e₂) :
    cons e₁ n₁ l₁ h₁ < cons e₂ n₂ l₂ h₂ := by
  rw [cons_lt_cons_iff, Prod.Lex.toLex_lt_toLex]
  tauto

theorem cons_lt_cons_snd {l₁ l₂ : CNFList E}
    {h₁ : expGT e l₁} {h₂ : expGT e l₂} {n₁ n₂ : ℕ+} (h : n₁ < n₂) :
    cons e n₁ l₁ h₁ < cons e n₂ l₂ h₂ := by
  rw [cons_lt_cons_iff, Prod.Lex.toLex_lt_toLex]
  tauto

theorem cons_lt_cons_thd {l₁ l₂ : CNFList E}
    {h₁ : expGT e l₁} {h₂ : expGT e l₂} {n : ℕ+} (h : l₁ < l₂) :
    cons e n l₁ h₁ < cons e n l₂ h₂ := by
  rw [cons_lt_cons_iff, Prod.Lex.toLex_lt_toLex]
  tauto

theorem cons_le_cons_iff {e₁ e₂ : E} {l₁ l₂ : CNFList E}
    {h₁ : expGT e₁ l₁} {h₂ : expGT e₂ l₂} {n₁ n₂ : ℕ+} :
    cons e₁ n₁ l₁ h₁ ≤ cons e₂ n₂ l₂ h₂ ↔
      toLex (e₁, n₁) < toLex (e₂, n₂) ∨ e₁ = e₂ ∧ n₁ = n₂ ∧ l₁ ≤ l₂ := by
  apply List.cons_le_cons_iff.trans
  simp [and_assoc]

/-- A recursion principle on `CNFList` stating that every element can be uniquely built from
`CNFList.cons`. -/
@[elab_as_elim]
def consRecOn {p : CNFList E → Sort*} (l : CNFList E) (zero : p 0)
    (cons : ∀ e n l (h : expGT e l), p l → p (cons e n l h)) : p l :=
  match l with
  | ⟨[], _⟩ => zero
  | ⟨x :: l, hl⟩ => cons _ x.2 _ hl.expGT (consRecOn ⟨l, hl.of_cons⟩ zero cons)
termination_by l.1

@[simp]
theorem consRecOn_zero {p : CNFList E → Sort*} (zero : p 0)
    (cons : ∀ e n l (h : expGT e l), p l → p (cons e n l h)) : consRecOn 0 zero cons = zero :=
  by rw [consRecOn.eq_def]

@[simp]
theorem consRecOn_cons {p : CNFList E → Sort*} (zero : p 0)
    (cons : ∀ e n l (h : expGT e l), p l → p (cons e n l h)) {e l} (h : expGT e l) (n : ℕ+) :
    consRecOn (.cons e n l h) zero cons = cons _ n _ h (consRecOn l zero cons) :=
  by rw [consRecOn.eq_def]; rfl

theorem expGT_iff_lt_single : expGT e l ↔ l < single e 1 := by
  induction l using consRecOn with
  | zero => simp [single]
  | cons f n l hl => simp [single_eq_cons, cons_lt_cons_iff, Prod.Lex.toLex_lt_toLex]

end LinearOrder

section Notation
variable [Notation E]

@[simp]
theorem expGT_eq_zero_iff : expGT (0 : E) l ↔ l = 0 := by
  induction l using consRecOn <;> simp [← bot_eq_zero]

@[simp]
theorem cons_zero (n : ℕ+) {l : CNFList E} (hl : expGT 0 l) : cons 0 n l hl = n := by
  obtain rfl := expGT_eq_zero_iff.1 hl
  rw [← single_zero, single_eq_cons]

@[simp]
theorem expGT_zero_left : expGT 0 l ↔ l = 0 := by
  induction l using consRecOn <;> simp

end Notation

-- toLex → single is monotonic

/-! ### Notation instance -/

section Notation
variable [Notation E]

/-- This is made private, as we'll instead use `Notation.eval` once we're able to build the
instance. -/
private def evalAux (l : CNFList E) : Ordinal :=
  (l.1.map fun x ↦ ω ^ eval (ofLex x).1 * (ofLex x).2).sum

private theorem evalAux_cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    evalAux (cons e n l h) = ω ^ eval e * n + evalAux l :=
  rfl

private theorem le_evalAux_cons {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    ω ^ eval e ≤ evalAux (cons e n l h) :=
  le_add_of_le_left <| le_mul_of_one_le_right' (mod_cast n.one_le)

private theorem evalAux_lt' {l : CNFList E} {o : Ordinal}
    (h : ∀ x ∈ l.1.head?, eval (ofLex x).1 < o) : evalAux l < ω ^ o := by
  induction l using consRecOn with
  | zero => exact opow_pos _ omega0_pos
  | cons f n l hf IH =>
    simp at h
    apply principal_add_omega0_opow
    · exact omega0_opow_mul_nat_lt h n
    · exact IH fun x hx ↦ (eval_strictMono (hf x hx)).trans h

private theorem expGT.evalAux_lt {l : CNFList E} (h : expGT e l) : evalAux l < ω ^ eval e :=
  evalAux_lt' (by simpa [expGT] using h)

private theorem expGT_iff_evalAux_lt {l : CNFList E} : expGT e l ↔ evalAux l < ω ^ eval e where
  mp := expGT.evalAux_lt
  mpr h := by
    cases l using consRecOn with
    | zero => simp
    | cons f l hf n =>
      rw [expGT_cons_iff]
      exact eval_lt_eval.1 <| (opow_lt_opow_iff_right one_lt_omega0).1 <|
        (le_evalAux_cons _ _).trans_lt h

private theorem evalAux_lt_opow_top (l : CNFList E) : evalAux l < ω ^ Notation.top E :=
  evalAux_lt' fun _ _ ↦ eval_lt_top _

private theorem strictMono_evalAux : StrictMono (evalAux (E := E)) := by
  intro l m hlm
  induction m using consRecOn generalizing l with
  | zero => simp at hlm
  | cons f k m hf =>
    induction l using consRecOn with
    | zero =>
      apply (Ordinal.mul_pos _ _).trans_le (le_add_right _ _)
      · exact opow_pos _ omega0_pos
      · exact_mod_cast k.pos
    | cons e n l he =>
      simp_rw [evalAux_cons]
      obtain (h | ⟨rfl, rfl, h⟩) := cons_lt_cons_iff.1 hlm
      · calc
          _ < ω ^ eval e * (n + 1) := by
            rw [mul_add_one, add_lt_add_iff_left]
            exact he.evalAux_lt
          _ ≤ ω ^ eval f * k := by
            obtain (h | ⟨rfl, h⟩) := Prod.Lex.toLex_lt_toLex.1 h
            · apply (lt_of_lt_of_le _ (le_mul_of_one_le_right' (mod_cast k.one_le))).le
              simpa [evalAux] using ((expGT_single_iff (n := n.1.succPNat)).2 h).evalAux_lt
            · exact mul_le_mul_left' (mod_cast h.nat_succ_le) _
          _ ≤ _ := le_self_add
      · simp_all

private theorem mem_range_evalAux_of_lt {o} (h : o < ω ^ Notation.top E) :
    o ∈ Set.range (evalAux (E := E)) := by
  induction o using CNFRec ω with
  | H0 => use 0; rfl
  | H o ho IH =>
    obtain ⟨e, he⟩ := Notation.mem_range_eval_iff_lt.2 <| (lt_opow_iff_log_lt one_lt_omega0 ho).1 h
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt o one_lt_omega0)
    obtain ⟨l, hl⟩ := IH ((mod_opow_log_lt_self ω ho).trans h)
    have h : expGT e l := by
      rw [expGT_iff_evalAux_lt, hl, ← he]
      exact mod_lt _ (opow_ne_zero _ omega0_ne_zero)
    refine ⟨cons _ ⟨n, ?_⟩ _ h, ?_⟩
    · rw [← Nat.cast_lt (α := Ordinal), ← hn, Nat.cast_zero]
      exact div_opow_log_pos _ ho
    · rw [evalAux_cons, he, PNat.mk_coe, ← hn, hl, Ordinal.div_add_mod]

private theorem mem_range_evalAux_iff (o) :
    o ∈ Set.range (evalAux (E := E)) ↔ o < ω ^ Notation.top E := by
  refine ⟨?_, mem_range_evalAux_of_lt⟩
  rintro ⟨l, rfl⟩
  exact evalAux_lt_opow_top l

/-- `evalAux` as a `PrincipalSeg`. -/
private noncomputable def eval' : CNFList E <i Ordinal.{0} :=
  ⟨(OrderEmbedding.ofStrictMono _ strictMono_evalAux).ltEmbedding, _, mem_range_evalAux_iff⟩

/-- If `E` is an ordinal notation, then `CNFList E` is as well, by evaluating
`ω ^ e₀ * n₀ + ω ^ e₁ * n₁ + ⋯` in the obvious manner. -/
noncomputable instance : Notation (CNFList E) := by
  apply ofEval eval' <;> simp [eval', evalAux]

private theorem eval_eq_evalAux (l : CNFList E) : eval l = evalAux l :=
  eval.eq eval' l

theorem eval_cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    eval (cons e n l h) = ω ^ eval e * n + eval l := by
  simp_rw [eval_eq_evalAux]; rfl

theorem eval_cons_ne_zero {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    eval (cons e n l h) ≠ 0 := by
  simp

@[simp]
theorem eval_single (e : E) (n : ℕ+) : eval (single e n) = ω ^ eval e * n := by
  simp [single_eq_cons, eval_cons]

theorem le_eval_cons {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    ω ^ eval e ≤ eval (cons e n l h) := by
  simp_rw [eval_eq_evalAux]; exact le_evalAux_cons h n

theorem expGT_iff_eval_lt {l : CNFList E} : expGT e l ↔ eval l < ω ^ eval e := by
  simp_rw [eval_eq_evalAux]; exact expGT_iff_evalAux_lt

alias ⟨expGT.eval_lt, _⟩ := expGT_iff_eval_lt

theorem eval_cons_lt (he : e < f) (h : expGT e l) : eval (cons e n l h) < ω ^ eval f := by
  apply expGT.eval_lt
  simpa

theorem eval_lt_opow_top (l : CNFList E) : evalAux l < ω ^ Notation.top E :=
  evalAux_lt_opow_top l

@[simp]
theorem log_omega0_eval_cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    log ω (eval (cons e n l h)) = eval e := by
  rw [eval_cons, log_opow_mul_add one_lt_omega0 (mod_cast n.ne_zero) h.eval_lt,
    log_eq_zero (nat_lt_omega0 n), add_zero]

instance : LawfulNatCast (CNFList E) where
  eval_natCast
    | 0 => by simp
    | n + 1 => by apply (eval_single _ _).trans; simp

end Notation

/-! ### Split -/

section Split
variable [Notation E]

private theorem one_le_eval (h : e ≠ 0) : 1 ≤ eval e := by
  rwa [Ordinal.one_le_iff_ne_zero, eval_ne_zero_iff]

private theorem omega0_opow_eval_of_ne_zero (h : e ≠ 0) : ω ^ eval e = ω * ω ^ (eval e - 1) := by
  conv_lhs => rw [← Ordinal.add_sub_cancel_of_le (one_le_eval h), opow_add, opow_one]

theorem eval_cons_cons_mod_omega0 (hl hm) :
    eval (cons f k (cons e n l hl) hm) % ω = eval (cons e n l hl) % ω := by
  rw [expGT_cons_iff] at hm
  rw [eval_cons, omega0_opow_eval_of_ne_zero hm.ne_bot, mul_assoc, mul_add_mod_self]

/-- An auxiliary function for `splitSnd`. -/
private def splitSndAux (l : List (E ×ₗ ℕ+)) : ℕ :=
  match l.getLast? with
  | none => 0
  | some a => if (ofLex a).1 = 0 then (ofLex a).2 else 0

private theorem splitSndAux_single (e : E) (n : ℕ+) :
    splitSndAux (single e n).1 = eval (single e n) % ω := by
  simp [single, splitSndAux, eval_cons]
  split
  · have := mod_eq_of_lt (nat_lt_omega0.{0} n)
    simp_all
  · rwa [omega0_opow_eval_of_ne_zero, mul_assoc, mul_mod]

private theorem splitSndAux_cons_cons (hl hm) :
    splitSndAux (cons f k (cons e n l hl) hm).1 = splitSndAux (cons e n l hl).1 := by
  simp [splitSndAux]

private theorem splitSndAux_eq (l : CNFList E) : splitSndAux l.1 = eval l % ω := by
  induction l using consRecOn with
    | zero => simp [splitSndAux]
    | cons e n l hl IH =>
      cases l using consRecOn with
      | zero => exact splitSndAux_single e n
      | cons f k m hm => rw [eval_cons_cons_mod_omega0, splitSndAux_cons_cons, IH]

/-- An auxiliary function for `splitFst`. -/
private def splitFstAux (l : CNFList E) : CNFList E :=
  if splitSndAux l.1 = 0 then l else ⟨_, l.2.dropLast⟩

private def expGT.dropLast {l : CNFList E} (h : expGT e l) : expGT e ⟨_, l.2.dropLast⟩ := by
  cases l using consRecOn with
  | zero => exact expGT_zero_right _
  | cons f n l hl =>
    cases l using consRecOn with
    | zero => exact expGT_zero_right _
    | cons => simp_all [expGT]

private theorem expGT.splitFstAux {l : CNFList E} (h : expGT e l) : expGT e (splitFstAux l) := by
  rw [CNFList.splitFstAux]
  split
  · exact h
  · exact h.dropLast

private theorem eval_splitFstAux_single (e : E) (n : ℕ+) :
    eval (splitFstAux (single e n)) = ω * (eval (single e n) / ω) := by
  dsimp [single, splitFstAux, splitSndAux]
  split
  · simp_all [Ordinal.div_eq_zero_of_lt (nat_lt_omega0 n)]
  · rw [if_pos rfl, eval_cons, omega0_opow_eval_of_ne_zero, mul_assoc, mul_add_div _ omega0_ne_zero]
    · simp
    · assumption

private theorem splitFstAux_cons_cons (hl hm) :
    splitFstAux (cons f k (cons e n l hl) hm) = cons f k _ hm.splitFstAux := by
  rw [splitFstAux, splitSndAux_cons_cons]
  aesop (add simp [splitFstAux])

private theorem eval_splitFstAux (l : CNFList E) : eval (splitFstAux l) = ω * (eval l / ω) := by
  induction l using consRecOn with
  | zero => simp [splitFstAux]
  | cons e n l hl IH =>
    cases l using consRecOn with
    | zero => exact eval_splitFstAux_single e _
    | cons f k m hm =>
      rw [expGT_cons_iff] at hl
      rw [splitFstAux_cons_cons, eval_cons, IH]
      conv_rhs => rw [eval_cons, omega0_opow_eval_of_ne_zero hl.ne_bot, mul_assoc,
        Ordinal.mul_add_div _ omega0_ne_zero, mul_add, ← mul_assoc, ← opow_one_add,
        Ordinal.add_sub_cancel_of_le (one_le_eval hl.ne_bot)]

instance : Split (CNFList E) where
  splitFst := splitFstAux
  splitSnd l := splitSndAux l.1
  eval_splitFst := eval_splitFstAux
  splitSnd_eq := splitSndAux_eq

theorem expGT.splitFst {l : CNFList E} (h : expGT e l) : expGT e (splitFst l) :=
  h.splitFstAux

@[simp]
theorem splitFst_cons_cons (hl hm) :
    splitFst (cons f k (cons e n l hl) hm) = cons f k _ hm.splitFst :=
  splitFstAux_cons_cons ..

@[simp]
theorem splitSnd_cons_cons (hl hm) :
    splitSnd (cons f k (cons e n l hl) hm) = splitSnd (cons e n l hl) :=
  splitSndAux_cons_cons _ _

end Split

/-! ### Addition -/

section Add
section LinearOrder
variable [LinearOrder E]

/-- We make this private as we don't yet prove this gives a valid `CNFList` for `CNFList` inputs. -/
private def addAux : List (E ×ₗ ℕ+) → List (E ×ₗ ℕ+) → List (E ×ₗ ℕ+)
  | [], l => l
  | a :: l, [] => a :: l
  | a :: l, b :: m =>
    match cmp (ofLex a).1 (ofLex b).1 with
    | .lt => b :: m
    | .eq => toLex ((ofLex b).1, (ofLex a).2 + (ofLex b).2) :: m
    | .gt => a :: addAux l (b :: m)

-- private theorem nil_addAux (l : List (E ×ₗ ℕ+)) : addAux [] l = l := rfl
private theorem addAux_nil (l : List (E ×ₗ ℕ+)) : addAux l [] = l := by cases l <;> rfl

private theorem expGT_addAux {l m : CNFList E} (hl : expGT e l) (hm : expGT e m)
    (H : IsCNFList (addAux l.1 m.1)) : expGT e ⟨addAux l.1 m.1, H⟩ := by
  cases l using consRecOn with
  | zero => exact hm
  | cons e l h n =>
    induction m using consRecOn with
    | zero => exact hl
    | cons f m k hm =>
      dsimp [expGT, addAux]
      split <;> simp_all

private theorem isCNFList_addAux (l m : CNFList E) : IsCNFList (addAux l.1 m.1) := by
  induction l using consRecOn with
  | zero => exact m.2
  | cons e n l hl IH =>
    induction m using consRecOn with
    | zero => rw [val_zero, addAux_nil]; exact CNFList.isCNFList _
    | cons f m k hm =>
      dsimp [addAux]
      split
      on_goal 3 => apply (expGT_addAux hl _ IH).isCNFList; simp_all
      all_goals exact (cons _ _ _ hm).isCNFList

/-- We define addition on `CNFList E` recursively, so that `x + 0 = 0 + x = x` and:

* If `e < f`, then `(ω ^ e * n + l) + (ω ^ f * k + m) = ω ^ e * k + m`.
* If `e = f`, then `(ω ^ e * n + l) + (ω ^ f * k + m) = ω ^ e * (n + k) + m`.
* If `e > f`, then `(ω ^ e * n + l) + (ω ^ f * k + m) = ω ^ e * n + (l + (ω ^ f * k + m))`.

If `E` is an ordinal notation, then addition on `CNFList E` is lawful.
-/
instance : Add (CNFList E) where
  add l m := ⟨_, isCNFList_addAux l m⟩

instance : AddZeroClass (CNFList E) where
  zero_add _ := rfl
  add_zero l := ext (addAux_nil l.1)

theorem expGT_add {l m : CNFList E} (hl : expGT e l) (hm : expGT e m) : expGT e (l + m) :=
  expGT_addAux hl hm _

private theorem cons_add_cons (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl + cons f k m hm = match he : cmp e f with
      | .lt => cons f k m hm
      | .eq => cons f (n + k) m hm
      | .gt => cons e n (l + cons f k m hm) (expGT_add hl (by simpa using he)) := by
  rw [Subtype.eq_iff]
  show addAux _ _ = _
  dsimp [addAux]
  aesop (add simp [lt_asymm])

theorem cons_add_cons_of_lt (he : e < f) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl + cons f k m hm = cons f k m hm := by
  rw [cons_add_cons]
  split <;> rename_i heq <;> rw [he.cmp_eq_lt] at heq <;> contradiction

@[simp]
theorem cons_add_cons_eq (hl : expGT e l) (n : ℕ+) (hm : expGT e m) (k : ℕ+) :
    cons e n l hl + cons e k m hm = cons e (n + k) m hm := by
  rw [cons_add_cons]; aesop

theorem cons_add_cons_of_gt (he : f < e) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl + cons f k m hm =
      cons _ n (l + cons f k m hm) (expGT_add hl (by simpa using he)) := by
  rw [cons_add_cons]
  split <;> rename_i heq <;> rw [he.cmp_eq_gt] at heq <;> contradiction

end LinearOrder

variable [Notation E]

instance : LawfulAdd (CNFList E) where
  eval_add l m := by
    induction l using consRecOn with
    | zero => simp
    | cons e n l hl IH =>
      induction m using consRecOn with
      | zero => simp
      | cons f k m hm =>
        obtain he | rfl | he := lt_trichotomy e f
        · rw [cons_add_cons_of_lt he]
          exact (add_absorp (eval_cons_lt he _) (le_eval_cons _ _)).symm
        · rw [cons_add_cons_eq, eval_cons, eval_cons, eval_cons, add_assoc, add_absorp hl.eval_lt,
            ← add_assoc, PNat.add_coe, Nat.cast_add, mul_add]
          simpa [eval_cons] using le_eval_cons hm _
        · rw [cons_add_cons_of_gt he, eval_cons]
          simp_rw [IH, eval_cons, add_assoc]

theorem cons_eq_add (hl : expGT e l) (n : ℕ+) : cons e n l hl = single e n + l := by
  rw [← eval_inj]; simp [eval_cons]

end Add

/-! ### Subtraction -/

section Sub
section LinearOrder
variable [LinearOrder E]

/-- We make this private as we don't yet prove this gives a valid `CNFList` for `CNFList` inputs. -/
private def subAux : List (E ×ₗ ℕ+) → List (E ×ₗ ℕ+) → List (E ×ₗ ℕ+)
  | [], _ => []
  | a :: l, [] => a :: l
  | a :: l, b :: m =>
    match cmp (ofLex a).1 (ofLex b).1 with
    | .lt => []
    | .eq =>
      match cmp (ofLex a).2 (ofLex b).2 with
      | .lt => []
      | .eq => subAux l m
      | .gt => toLex ((ofLex a).1, (ofLex a).2 - (ofLex b).2) :: l
    | .gt => a :: l

private theorem subAux_nil (l : List (E ×ₗ ℕ+)) : subAux l [] = l := by cases l <;> rfl

private theorem isCNFList_subAux (l m : CNFList E) : IsCNFList (subAux l.1 m.1) := by
  induction l using consRecOn generalizing m with
  | zero => exact .nil
  | cons e n l hl IH =>
    cases m using consRecOn with
    | zero => rw [val_zero, subAux_nil]; exact CNFList.isCNFList _
    | cons f k m hm =>
      dsimp [subAux]
      have := fun n ↦ (cons e n l hl).isCNFList
      aesop

/-- We define subtraction on `CNFList E` recursively, so that `x - 0 = x`, `0 - x = 0`, and:

* If `e < f`, then `(ω ^ e * n + l) - (ω ^ f * k + m) = 0`.
* If `e = f`, then
  * If `n < k`, then `(ω ^ e * n + l) + (ω ^ f * k + m) = 0`.
  * If `n = k`, then `(ω ^ e * n + l) + (ω ^ f * k + m) = l - m`.
  * If `n > k`, then `(ω ^ e * n + l) + (ω ^ f * k + m) = ω ^ e * (n - k) + l`.
* If `e > f`, then `(ω ^ e * n + l) + (ω ^ f * k + m) = ω ^ e * n + l`.

If `E` is an ordinal notation, then subtraction on `CNFList E` is lawful.
-/
instance : Sub (CNFList E) where
  sub l m := ⟨_, isCNFList_subAux l m⟩

private theorem zero_sub' (l : CNFList E) : 0 - l = 0 := rfl
private theorem sub_zero' (l : CNFList E) : l - 0 = l := ext (subAux_nil l.1)

private theorem cons_sub_cons (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl - cons f k m hm = match cmp e f with
      | .lt => 0
      | .eq =>
        match cmp n k with
        | .lt => 0
        | .eq => l - m
        | .gt => cons e (n - k) l hl
      | .gt => cons e n l hl := by
  rw [Subtype.eq_iff]
  show subAux _ _ = _
  dsimp [subAux]
  aesop

theorem cons_sub_cons_of_lt (he : e < f) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl - cons f k m hm = 0 := by
  rw [cons_sub_cons, he.cmp_eq_lt]

private theorem cons_sub_cons_of_eq (hl : expGT e l) (n : ℕ+) (hm : expGT e m) (k : ℕ+) :
    cons e n l hl - cons e k m hm = match cmp n k with
      | .lt => 0
      | .eq => l - m
      | .gt => cons e (n - k) l hl := by
  rw [cons_sub_cons, cmp_self_eq_eq]

theorem cons_sub_cons_of_gt (he : f < e) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl - cons f k m hm = cons e n l hl := by
  rw [cons_sub_cons, he.cmp_eq_gt]

theorem cons_sub_cons_eq_of_lt {n k : ℕ+} (hn : n < k) (hl : expGT e l) (hm : expGT e m) :
    cons e n l hl - cons e k m hm = 0 := by
  rw [cons_sub_cons_of_eq, hn.cmp_eq_lt]

@[simp]
theorem cons_sub_cons_eq_eq (hl : expGT e l) (hm : expGT e m) (n : ℕ+) :
    cons e n l hl - cons e n m hm = l - m := by
  rw [cons_sub_cons_of_eq, cmp_self_eq_eq]

theorem cons_sub_cons_eq_of_gt {n k : ℕ+} (hn : k < n) (hl : expGT e l) (hm : expGT e m) :
    cons e n l hl - cons e k m hm = cons e (n - k) l hl := by
  rw [cons_sub_cons_of_eq, hn.cmp_eq_gt]

end LinearOrder

variable [Notation E]

instance : LawfulSub (CNFList E) where
  eval_sub l m := by
    induction l using consRecOn generalizing m with
    | zero => simp [zero_sub']
    | cons e n l hl IH =>
      induction m using consRecOn with
      | zero => simp [sub_zero']
      | cons f k m hm =>
        obtain he | rfl | he := lt_trichotomy e f
        · rw [cons_sub_cons_of_lt he, eval_zero, eq_comm, Ordinal.sub_eq_zero_iff_le]
          exact (eval_strictMono (cons_lt_cons_fst he)).le
        · obtain hn | rfl | hn := lt_trichotomy n k
          · rw [cons_sub_cons_eq_of_lt hn, eval_zero, eq_comm, Ordinal.sub_eq_zero_iff_le]
            exact (eval_strictMono (cons_lt_cons_snd hn)).le
          · rw [cons_sub_cons_eq_eq, eval_cons, eval_cons, Ordinal.add_sub_add_cancel, IH]
          · rw [cons_sub_cons_eq_of_gt hn, eq_comm]
            apply sub_eq_of_add_eq
            rw [← eval_add, cons_add_cons_eq, PNat.add_sub_of_lt hn]
        · rw [cons_sub_cons_of_gt he, eq_comm]
          apply sub_eq_of_add_eq
          rwa [← eval_add, cons_add_cons_of_lt]

end Sub

/-! ### Multiplication -/

section Mul
variable [Notation E] [Add E]

/-- We make this private as we don't yet prove this gives a valid `CNFList` for `CNFList` inputs. -/
private def mulAux : List (E ×ₗ ℕ+) → List (E ×ₗ ℕ+) → List (E ×ₗ ℕ+)
  | [], _ | _, [] => []
  | a :: l, b :: m => if (ofLex b).1 = 0
      then toLex ((ofLex a).1, (ofLex a).2 * (ofLex b).2) :: l
      else toLex ((ofLex a).1 + (ofLex b).1, (ofLex b).2) :: mulAux (a :: l) m

private theorem nil_mulAux (l : List (E ×ₗ ℕ+)) : mulAux [] l = [] := by cases l <;> rfl
private theorem mulAux_nil (l : List (E ×ₗ ℕ+)) : mulAux l [] = [] := by cases l <;> rfl

variable [LawfulAdd E]

private theorem expGT.cons_mulAux (hl : expGT e l) (hm : expGT f m) {n : ℕ+}
    (H : IsCNFList (mulAux (cons e n l hl).1 m.1)) : expGT (e + f) ⟨_, H⟩ := by
  induction m using consRecOn <;> aesop (add simp [mulAux_nil, mulAux])

private theorem isCNFList_mulAux (l m : CNFList E) : IsCNFList (mulAux l.1 m.1) := by
  induction l using consRecOn generalizing m with
  | zero => simp [nil_mulAux]
  | cons e n l hl IH =>
    induction m using consRecOn with
    | zero => simp [mulAux_nil]
    | cons f k m hm IH' =>
      dsimp [mulAux]
      split
      · exact hl.isCNFList n
      · exact (expGT.cons_mulAux _ hm _).isCNFList (l := ⟨_, IH'⟩) _

/-- We define multiplication on `CNFList E` recursively, so that `x * 0 = 0 * x = 0` and:

* For `k : ℕ+`, then `(ω ^ e * n + l) * k = ω ^ e * (n * k) + l`.
* If `f ≠ 0`, then `(ω ^ e * n + l) * (ω ^ f * k + m) = ω ^ (e + f) * k + (ω ^ e * n + l) * m`.

If `E` is an ordinal notation with lawful addition, then multiplication on `CNFList E` is lawful.
-/
instance : Mul (CNFList E) where
  mul l m := ⟨_, isCNFList_mulAux l m⟩

private theorem zero_mul' (l : CNFList E) : 0 * l = 0 := ext (nil_mulAux l.1)
private theorem mul_zero' (l : CNFList E) : l * 0 = 0 := ext (mulAux_nil l.1)

private theorem cons_mul_cons' (hl : expGT e l) (hm : expGT f m) (n k : ℕ+) :
    (cons e n l hl * cons f k m hm).1 = if f = 0
      then toLex (e, n * k) :: l.1
      else toLex (e + f, k) :: (cons e n l hl * m).1 :=
  rfl

theorem expGT.cons_mul (hl : expGT e l) (hm : expGT f m) (n : ℕ+) :
    expGT (e + f) (cons e n l hl * m) :=
  hl.cons_mulAux hm _

theorem expGT.mul_natCast (hl : expGT e l) (n : ℕ) : expGT e (l * n) := by
  cases l using consRecOn with
  | zero => simp [zero_mul']
  | cons f l h k =>
    cases n with
    | zero => simp [mul_zero']
    | succ n =>
      rw [← n.succ_eq_add_one, ← n.succPNat_coe, ← single_zero, single_eq_cons,
        expGT, cons_mul_cons']
      simp_all

theorem cons_mul_cons (hl : expGT e l) (hm : expGT f m) (n k : ℕ+) :
    cons e n l hl * cons f k m hm = if f = 0
      then cons e (n * k) l hl
      else cons _ k _ (hl.cons_mul hm n)  := by
  apply ext
  rw [cons_mul_cons']
  split <;> rfl

@[simp]
theorem cons_mul_pNat (hl : expGT e l) (n k : ℕ+) : cons e n l hl * k = cons e (n * k) l hl := by
  rw [← single_zero, single_eq_cons, cons_mul_cons]; exact if_pos rfl

theorem cons_mul_natCast (hl : expGT e l) (n : ℕ+) {k : ℕ} (hk : 0 < k) :
    cons e n l hl * k = cons e (n * ⟨k, hk⟩) l hl :=
  cons_mul_pNat hl n ⟨k, hk⟩

theorem cons_mul_cons_of_ne_zero (hl : expGT e l) (hm : expGT f m) (hf : f ≠ 0) (n k : ℕ+) :
    cons e n l hl * cons f k m hm = cons _ k _ (hl.cons_mul hm n) := by
  rw [cons_mul_cons]; exact if_neg hf

instance : LawfulMul (CNFList E) where
  eval_mul l m := by
    induction m using consRecOn generalizing l with
    | zero => simp [mul_zero']
    | cons f k m hm IH =>
      cases l using consRecOn with
      | zero => simp [zero_mul']
      | cons e n l hl =>
        obtain rfl | hf := eq_or_ne f 0
        · rw [cons_zero, cons_mul_pNat, eval_natCast]
          clear *-
          induction k using PNat.recOn with
          | one => simp
          | succ k IH' =>
            push_cast
            rw [mul_add_one, mul_add_one, ← IH', ← eval_add, cons_add_cons_eq]
        · rw [cons_mul_cons_of_ne_zero _ _ hf, eval_cons, eval_cons hm, mul_add, IH, ← mul_assoc,
            mul_omega0_opow, eval_add, eval_cons, log_opow_mul_add one_lt_omega0 _ hl.eval_lt,
            log_eq_zero, add_zero]
          · exact_mod_cast nat_lt_omega0 n
          · exact_mod_cast n.ne_zero
          · exact eval_cons_ne_zero hl n
          · simpa

theorem eval_cons_mul_natCast (hl : expGT e l) (n : ℕ+) {k : ℕ} (hk : 0 < k) :
    eval (cons e n l hl) * k = eval (cons e (n * ⟨k, hk⟩) l hl) := by
  rw [← cons_mul_natCast hl n hk, eval_mul, eval_natCast]

private theorem eval_npowRec (l : CNFList E) : ∀ n : ℕ, eval (npowRec n l) = eval l ^ n
  | 0 => by simp [npowRec]
  | n + 1 => by rw [npowRec, eval_mul, pow_add, pow_one, eval_npowRec]

end Mul

/-! ### Division -/

section Div
variable [Notation E]

/-- The result of `(ω ^ e * n + l) / (ω ^ e * k + m)`, for any sufficiently large `e`. -/
private def divNatAux (n k : ℕ+) (l m : List (E ×ₗ ℕ+)) : ℕ :=
  let r := n.val / k.val
  if toLex (k.val * r, m) ≤ toLex (n.val, l) then r else r - 1

private theorem divNatAux_eq {l m : CNFList E} (hl : expGT e l) (hm : expGT e m) (n k : ℕ+)
    [Add E] [LawfulAdd E] :
    eval (cons e n l hl) / eval (cons e k m hm) = divNatAux n k l.1 m.1 := by
  rw [divNatAux, Ordinal.div_eq_iff (eval_cons_ne_zero _ _)]
  obtain hn | hn := lt_or_le n k
  · have : n.val / k.val = 0 := (Nat.div_eq_zero_iff_lt k.pos).2 hn
    simpa [this] using cons_lt_cons_snd hn
  · have : 1 ≤ n.val / k.val := (Nat.one_le_div_iff k.pos).2 hn
    split <;> rw [← Nat.cast_add_one, eval_cons_mul_natCast _ _ (Nat.succ_pos _)]
    · rw [eval_cons_mul_natCast, eval_le_eval, eval_lt_eval]
      constructor
      · simp_all [cons_le_cons_iff, Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_le_toLex,
          ← PNat.coe_lt_coe, ← PNat.coe_inj]
      · apply cons_lt_cons_snd
        simpa using Nat.lt_mul_div_succ n k.pos
      · simpa
    · obtain h | h := this.eq_or_lt
      · simp_all [Prod.Lex.toLex_lt_toLex, cons_lt_cons_iff, ← PNat.coe_lt_coe, ← PNat.coe_inj]
      · refine ⟨le_of_lt ?_, ?_⟩
        · rw [eval_cons_mul_natCast _ _ (by simpa), eval_lt_eval]
          apply cons_lt_cons_snd
          rw [← PNat.coe_lt_coe]
          apply lt_of_lt_of_le _ (Nat.mul_div_le _ k)
          simpa
        · simp_all [Prod.Lex.toLex_lt_toLex, cons_lt_cons_iff, ← PNat.coe_lt_coe, ← PNat.coe_inj]

variable [Sub E]

/-- We make this private as we don't yet prove this gives a valid `CNFList` for `CNFList` inputs. -/
private def divAux : List (E ×ₗ ℕ+) → List (E ×ₗ ℕ+) → List (E ×ₗ ℕ+)
  | [], _ | _, [] => []
  | a :: l, b :: m =>
    match cmp (ofLex a).1 (ofLex b).1 with
    | .lt => []
    | .eq => (divNatAux (ofLex a).2 (ofLex b).2 l m : CNFList E).1
    | .gt => toLex ((ofLex a).1 - (ofLex b).1, (ofLex a).2) :: divAux l (b :: m)

private theorem nil_divAux (l : List (E ×ₗ ℕ+)) : divAux [] l = [] := by cases l <;> rfl
private theorem divAux_nil (l : List (E ×ₗ ℕ+)) : divAux l [] = [] := by cases l <;> rfl

variable [LawfulSub E]

private theorem expGT.divAux_cons (hl : expGT e l) (hm : expGT f m)
    (H : IsCNFList (divAux l.1 (cons f k m hm).1)) : expGT (e - f) ⟨_, H⟩ := by
  induction l using consRecOn with
  | zero => simp [nil_divAux]
  | cons f' k m hm =>
    dsimp [divAux, divNatAux, expGT]
    rw [val_natCast]
    have {a b c : E} (h₁ : a < b) (h₂ : b < c) : b - a < c - a := by
      rw [← eval_lt_eval, eval_sub, eval_sub]
      apply sub_lt_of_lt_add
      · rwa [Ordinal.add_sub_cancel_of_le (eval_monotone (h₁.trans h₂).le), eval_lt_eval]
      · rw [pos_iff_ne_zero, Ordinal.sub_ne_zero_iff_lt, eval_lt_eval]
        exact h₁.trans h₂
    aesop

private theorem isCNFList_divAux (l m : CNFList E) : IsCNFList (divAux l.1 m.1) := by
  induction l using consRecOn generalizing m with
  | zero => simp [nil_divAux]
  | cons e n l hl IH =>
    cases m using consRecOn with
    | zero => simp [divAux_nil]
    | cons f k m hm =>
      dsimp [divAux]
      split
      · exact .nil
      · exact CNFList.isCNFList _
      · exact (expGT.divAux_cons hl hm _).isCNFList (l := ⟨_, IH ⟨_, hm.isCNFList k⟩⟩) n

/-- We define division on `CNFList E` recursively, so that `x / 0 = 0 / x = 0` and:

* If `e < f`, then `(ω ^ e * n + l) / (ω ^ f * k + m) = 0`.
* If `e = f`, then `(ω ^ e * n + l) / (ω ^ f * k + m)` is either of `n / k` or `n / k - 1`,
  depending on whether `ω ^ e * (n / k) + l` exceeds `ω ^ f * k + m`.
* If `e > f`, then `(ω ^ e * n + l) / (ω ^ f * k + m) = ω ^ (e - f) + l / (ω ^ f * k + m)`.

If `E` is an ordinal notation with lawful addition and subtraction, then division on `CNFList E` is
lawful.
-/
instance : Div (CNFList E) where
  div l m := ⟨_, isCNFList_divAux l m⟩

private theorem zero_div' (l : CNFList E) : 0 / l = 0 := ext (nil_divAux l.1)
private theorem div_zero' (l : CNFList E) : l / 0 = 0 := ext (divAux_nil l.1)

private theorem expGT.div_cons (hl : expGT e l) (hm : expGT f m) (n : ℕ+) :
    expGT (e - f) (l / cons f n m hm) :=
  expGT.divAux_cons hl hm _

private theorem cons_div_cons (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl / cons f k m hm = match cmp e f with
      | .lt => 0
      | .eq => divNatAux n k l.1 m.1
      | .gt => cons _ n _ (hl.div_cons hm k) := by
  apply ext
  show divAux _ _ = _
  dsimp [divAux]
  split <;> rfl

theorem cons_div_cons_of_lt (he : e < f) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl / cons f k m hm = 0 := by
  rw [cons_div_cons, he.cmp_eq_lt]

private theorem cons_div_cons_eq (hl : expGT e l) (n : ℕ+) (hm : expGT e m) (k : ℕ+) :
    cons e n l hl / cons e k m hm = divNatAux n k l.1 m.1 := by
  rw [cons_div_cons, cmp_self_eq_eq]

theorem cons_div_cons_of_gt (he : f < e) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl / cons f k m hm = cons _ n _ (expGT.div_cons hl hm k) := by
  rw [cons_div_cons, he.cmp_eq_gt]

instance [Add E] [LawfulAdd E] : LawfulDiv (CNFList E) where
  eval_div l m := by
    induction l using consRecOn generalizing m with
    | zero => simp [zero_div']
    | cons e n l hl IH =>
      cases m using consRecOn with
      | zero => simp [div_zero']
      | cons f k m hm _ =>
        obtain he | rfl | he := lt_trichotomy e f
        · rw [cons_div_cons_of_lt he, eval_zero, eq_comm]
          exact Ordinal.div_eq_zero_of_lt <| eval_strictMono (cons_lt_cons_fst he)
        · rw [cons_div_cons_eq, divNatAux_eq, eval_natCast]
        · have : cons f k m hm * single (e - f) n + l = cons e n l hl := by
            rw [single_eq_cons, cons_mul_cons_of_ne_zero]
            · simp [add_sub_cancel_of_le he.le, cons_eq_add]
            · simpa
          rw [cons_div_cons_of_gt he, ← this, eval_add, eval_mul, Ordinal.mul_add_div, ← IH]
          · rw [← eval_add, cons_eq_add]
          · exact eval_cons_ne_zero hm k

end Div

/-! ### Exponentiation -/

section Pow
variable [Notation E] [Mul E] [LawfulMul E] [Div E] [LawfulDiv E]

-- Rename, PR to Mathlib
theorem _root_.Ordinal.zero_opow_eq (o : Ordinal) : (0 : Ordinal) ^ o = if o = 0 then 1 else 0 := by
  obtain rfl | hx := eq_or_ne o 0 <;> simp_all

theorem _root_.Ordinal.mul_div_of_dvd {a b : Ordinal} (h : a ∣ b) : a * (b / a) = b := by
  conv_rhs => rw [← Ordinal.div_add_mod b a]
  rw [mod_eq_zero_of_dvd h, add_zero]

private theorem _root_.Ordinal.natCast_opow_of_omega0_dvd
    {n : ℕ} (hn : 1 < n) {o : Ordinal} (h : ω ∣ o) : n ^ o = ω ^ (o / ω) := by
  conv_rhs => left; rw [← natCast_opow_omega0 hn]
  rwa [← opow_mul, mul_div_of_dvd]

-- PR to Mathlib
private theorem _root_.isSuccPrelimit_iff_omega0_dvd {o : Ordinal} : IsSuccPrelimit o ↔ ω ∣ o := by
  obtain rfl | ho := eq_or_ne o 0
  · simpa using isSuccPrelimit_bot
  · have : IsLimit o ↔ IsSuccPrelimit o := by simp [isLimit_iff, ho]
    rw [← this, isLimit_iff_omega0_dvd]
    simp [ho]

/-- Calculates `l ^ m` where `m` is a multiple of `ω`. -/
private def powOmegaAux (l : List (E ×ₗ ℕ+)) (m : E) : CNFList E :=
  match l with
  | [] => if m = 0 then 1 else 0
  | a :: _ =>
    if (ofLex a).1 = 0 then
      if (ofLex a).2 = 1 then 1 else single (m / omega) 1
    else single ((ofLex a).1 * m) 1

private theorem eval_powOmegaAux (l : CNFList E) {m : E} (hm : ω ∣ eval m) :
    eval (powOmegaAux l.1 m) = eval l ^ eval m := by
  cases l using consRecOn with
  | zero => simp [powOmegaAux, zero_opow_eq, apply_ite]
  | cons e n l hl =>
    rw [val_cons, powOmegaAux]
    split_ifs <;> rename_i _ h
    · simp_all
    · have : 1 < n := n.one_le.lt_of_ne' h
      have := (natCast_opow_of_omega0_dvd this hm).symm
      aesop
    · rw [opow_of_isSuccPrelimit]
      · simp
      · apply le_trans _ (le_eval_cons _ _)
        simpa using opow_le_opow_right omega0_pos (eval_monotone (one_le_iff_ne_zero.2 h))
      · rwa [isSuccPrelimit_iff_omega0_dvd]

variable [Add E] [LawfulAdd E]

/-- We define (heterogeneous) exponentiation on `CNFList E` in the following way. If `f` is a
multiple of `ω`, then `x ^ f` is so that `0 ^ f` is `1` or `0`, `1 ^ f = 1`, and:

* If `x` is a natural number, then `x ^ f = ω ^ (f / ω)`.
* Otherwise, `(ω ^ e * n + l) ^ f = ω ^ (e * f)`.

Then, the general exponential `x ^ (f + n)` is computed as `x ^ y * x ^ n`, where the latter term
is simply `npowRec`.

If `E` is an ordinal notation with lawful addition, multiplication, division, then exponentiation on
`CNFList E` is lawful.
-/
instance [Split E] : Pow (CNFList E) E where
  pow l m := powOmegaAux l.1 (splitFst m) * npowRec (splitSnd m) l

instance [Split E] : LawfulPow (CNFList E) E where
  eval_pow l m := by
    show eval (_ * _) = _
    rw [← eval_splitFst_add_splitSnd m, eval_mul, eval_powOmegaAux, eval_npowRec, ← opow_natCast,
      ← opow_add]
    simp

end Pow
end CNFList

/-! ### CNF-like types -/

/-- A type which is order-isomorphic to `CNFList Exp` for some type of exponents. Arithmetic can be
transferred through this isomorphism. -/
class CNFLike (α : Type u) extends Zero α, One α, Omega α, LinearOrder α where
  /-- The type of exponents in the Cantor form. -/
  Exp : Type u
  /-- The exponents form an ordinal notation. -/
  notationExp : Notation Exp := by infer_instance

  /-- The type is order-isomorphic to `CNFList Exp`. -/
  equivList : α ≃o CNFList Exp
  equivList_zero : equivList 0 = 0
  equivList_one : equivList 1 = 1
  equivList_omega : equivList omega = Notation.omega
export CNFLike (Exp equivList equivList_zero equivList_one equivList_omega)
attribute [instance] CNFLike.notationExp
attribute [simp] equivList_zero equivList_one equivList_omega

namespace CNFLike
variable [CNFLike α]

/-- The evaluation function used in `notationOfExp`. -/
private noncomputable def eval' : α <i Ordinal.{0} :=
  equivList.toInitialSeg.transPrincipal eval

instance notationOfExp [Notation (Exp α)] [CNFLike α] : Notation α := by
  apply ofEval eval' <;> simp [eval']

@[simp]
theorem eval_equivList (l : α) : eval (equivList l) = eval l := by
  simpa [eval'] using eval'.eq eval l

instance : NatCast α where natCast n := equivList.symm n
theorem natCast_def (n : ℕ) : (n : α) = equivList.symm n := rfl
instance : LawfulNatCast α where
  eval_natCast n := by simp [← eval_equivList, natCast_def]

instance : Add α where add l m := equivList.symm (equivList l + equivList m)
theorem add_def (l m : α) : l + m = equivList.symm (equivList l + equivList m) := rfl
instance : LawfulAdd α where
  eval_add l m := by simp [← eval_equivList, add_def]

instance : Sub α where sub l m := equivList.symm (equivList l - equivList m)
theorem sub_def (l m : α) : l - m = equivList.symm (equivList l - equivList m) := rfl
instance : LawfulSub α where
  eval_sub l m := by simp [← eval_equivList, sub_def]

section Mul
variable [Add (Exp α)] [LawfulAdd (Exp α)]

instance : Mul α where mul l m := equivList.symm (equivList l * equivList m)
theorem mul_def (l m : α) : l * m = equivList.symm (equivList l * equivList m) := rfl
instance : LawfulMul α where
  eval_mul l m := by simp [← eval_equivList, mul_def]

end Mul

section Div
variable [Sub (Exp α)] [LawfulSub (Exp α)]

instance : Div α where div l m := equivList.symm (equivList l / equivList m)
theorem div_def (l m : α) : l / m = equivList.symm (equivList l / equivList m) := rfl
instance [Add (Exp α)] [LawfulAdd (Exp α)] : LawfulDiv α where
  eval_div l m := by simp [← eval_equivList, div_def]

end Div

section Split

instance : Split α where
  splitFst l := equivList.symm (splitFst (equivList l))
  splitSnd l := splitSnd (equivList l)
  eval_splitFst l := by simp [← eval_equivList]
  splitSnd_eq l := by simp [← eval_equivList, splitSnd_eq]

theorem splitFst_def (l : α) : splitFst l = equivList.symm (splitFst (equivList l)) := rfl
theorem splitSnd_def (l : α) : splitSnd l = splitSnd (equivList l) := rfl

end Split

section Pow
variable [Add (Exp α)] [LawfulAdd (Exp α)] [Mul (Exp α)] [Div (Exp α)] [Split (Exp α)]

instance instPow : Pow α (Exp α) where pow l e := equivList.symm (equivList l ^ e)
theorem pow_def (l : α) (e : Exp α) : l ^ e = equivList.symm (equivList l ^ e) := rfl
instance instLawfulPow [LawfulMul (Exp α)] [LawfulDiv (Exp α)] : LawfulPow α (Exp α) where
  eval_pow := by simp [← eval_equivList, pow_def]

end Pow

end CNFLike
end Ordinal.Notation
