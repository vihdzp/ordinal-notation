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

open Set

namespace Ordinal.Notation

section Lists
variable {E : Type u} {e f : E} [LinearOrder E]

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

@[ext] theorem ext {l m : CNFList E} : l.val = m.val → l = m := Subtype.ext

/-- The `CNFList` corresponding to `ω ^ e * n`. -/
def single (e : E) (n : ℕ+) : CNFList E :=
  ⟨[toLex (e, n)], .singleton _⟩

@[simp] theorem val_single (e : E) (n : ℕ+) : (single e n).val = [toLex (e, n)] := rfl

instance : Zero (CNFList E) := ⟨⟨[], .nil⟩⟩
instance [Zero E] : One (CNFList E) := ⟨single 0 1⟩
instance : LinearOrder (CNFList E) := Subtype.instLinearOrder _

@[simp] theorem mk_nil : ⟨[], .nil⟩ = (0 : CNFList E) := rfl
@[simp] theorem zero_le (l : CNFList E) : 0 ≤ l := List.nil_le l.1
@[simp] theorem not_lt_zero (l : CNFList E) : ¬ l < 0 := List.not_lt_nil l.1

theorem isCNFList (l : CNFList E) : IsCNFList l.1 := l.2
@[simp] theorem val_zero : (0 : CNFList E).val = [] := rfl
@[simp] theorem val_one [Zero E] : (1 : CNFList E).val = [toLex (0, 1)] := rfl

/-- The first infinite ordinal `ω = ω ^ 1 * 1`. -/
def omega [One E] : CNFList E := single 1 1
@[simp] theorem omega_def [One E] : single (1 : E) 1 = omega := rfl
@[simp] theorem val_omega [One E] : (omega : CNFList E).val = [toLex (1, 1)] := rfl

/-- The cast from natural numbers is defined as `n = single 0 n`. -/
instance [Zero E] : NatCast (CNFList E) where
  natCast n := n.recOn 0 (fun n _ ↦ single 0 n.succPNat)

@[simp, norm_cast] theorem natCast_zero [Zero E] : (0 : ℕ) = (0 : CNFList E) := rfl
@[simp, norm_cast] theorem natCast_one [Zero E] : (1 : ℕ) = (1 : CNFList E) := rfl

@[simp] theorem val_PNat (n : ℕ+) [Zero E] : (PNat.val n : CNFList E).1 = [toLex (0, n)] := by
  rw [← n.succPNat_natPred]; rfl

@[simp]
theorem single_zero [Zero E] (n : ℕ+) : single (0 : E) n = PNat.val n := by
  rw [← n.succPNat_natPred]
  rfl

/-- The predicate that `e` is bigger than the leading exponent in `l` (if it exists). This is the
condition on which `⟨e, n⟩ :: l` can be a `CNFList`. -/
def expGT (e : E) (l : CNFList E) : Prop :=
  ∀ f ∈ l.1.head?, (ofLex f).1 < e

@[simp] theorem expGT_zero (e : E) : expGT e 0 := by simp [expGT]
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

@[simp]
theorem cons_ne_zero (hl : expGT e l) (n : ℕ+) : cons e n l hl ≠ 0 := by
  rw [ne_eq, CNFList.ext_iff]; simp

@[simp]
theorem zero_ne_cons (hl : expGT e l) (n : ℕ+) : 0 ≠ cons e n l hl := by
  rw [ne_eq, CNFList.ext_iff]; simp

theorem single_eq_cons (e : E) (n : ℕ+) : single e n = cons e n 0 (expGT_zero e) :=
  rfl

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

@[simp]
theorem expGT_single_iff {e₁ e₂ : E} {n : ℕ+} : expGT e₁ (single e₂ n) ↔ e₂ < e₁ := by
  simp [expGT]

@[simp]
theorem expGT_eq_zero_iff [Notation E] : expGT (0 : E) l ↔ l = 0 := by
  induction l using consRecOn <;> simp [← bot_eq_zero]

@[simp]
theorem cons_zero [Notation E] (n : ℕ+) {l : CNFList E} (hl : expGT 0 l) : cons 0 n l hl = n := by
  obtain rfl := expGT_eq_zero_iff.1 hl
  rw [← single_zero, single_eq_cons]

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
    · rw [evalAux_cons, he, PNat.mk_coe, ← hn, hl, div_add_mod]

private theorem mem_range_evalAux_iff (o) :
    o ∈ Set.range (evalAux (E := E)) ↔ o < ω ^ Notation.top E := by
  refine ⟨?_, mem_range_evalAux_of_lt⟩
  rintro ⟨l, rfl⟩
  exact evalAux_lt_opow_top l

/-- If `E` is an ordinal notation, then `CNFList E` is as well, by evaluating
`ω ^ e₀ * n₀ + ω ^ e₁ * n₁ + ⋯` in the obvious manner. -/
@[simps! eval_top]
noncomputable instance [Notation E] : Notation (CNFList E) where
  eval := ⟨(OrderEmbedding.ofStrictMono _ strictMono_evalAux).ltEmbedding, _, mem_range_evalAux_iff⟩
  eval_zero := List.sum_nil
  eval_one := by simp [evalAux]

@[simp 900]
theorem eval_cons {e : E} {l : CNFList E} (h : expGT e l) (n : ℕ+) :
    eval (cons e n l h) = ω ^ eval e * n + eval l :=
  rfl

@[simp]
theorem eval_single (e : E) (n : ℕ+) : eval (single e n) = ω ^ eval e * n := by
  rw [single_eq_cons]; simp

theorem le_eval_cons {l : CNFList E} (h : expGT e l) (n : ℕ+) : ω ^ eval e ≤ eval (cons e n l h) :=
  le_evalAux_cons h n

theorem expGT_iff_eval_lt {l : CNFList E} : expGT e l ↔ eval l < ω ^ eval e :=
  expGT_iff_evalAux_lt

alias ⟨expGT.eval_lt, _⟩ := expGT_iff_eval_lt

theorem eval_cons_lt (he : e < f) (h : expGT e l) : eval (cons e n l h) < ω ^ eval f := by
  apply expGT.eval_lt
  simpa

theorem eval_lt_opow_top (l : CNFList E) : evalAux l < ω ^ Notation.top E :=
  evalAux_lt_opow_top l

instance : LawfulNatCast (CNFList E) where
  eval_natCast n := match n with
    | 0 => rfl
    | n + 1 => by apply (eval_single _ _).trans; simp

end Notation

/-! ### Addition -/

section Add

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

private theorem cons_addAux_cons (a b : E ×ₗ ℕ+) (l m : List (E ×ₗ ℕ+)) :
    addAux (a :: l) (b :: m) = match cmp (ofLex a).1 (ofLex b).1 with
      | .lt => b :: m
      | .eq => toLex ((ofLex b).1, (ofLex a).2 + (ofLex b).2) :: m
      | .gt => a :: addAux l (b :: m) :=
  rfl

private theorem expGT_addAux {l m : CNFList E} (hl : expGT e l) (hm : expGT e m)
    (H : IsCNFList (addAux l.1 m.1)) : expGT e ⟨addAux l.1 m.1, H⟩ := by
  cases l using consRecOn with
  | zero => exact hm
  | cons e l h n =>
    induction m using consRecOn with
    | zero => exact hl
    | cons f m k hm =>
      dsimp [expGT, cons_addAux_cons]
      split <;> simp_all

private theorem isCNFList_addAux (l m : CNFList E) : IsCNFList (addAux l.1 m.1) := by
  induction l using consRecOn with
  | zero => exact m.2
  | cons e n l hl IH =>
    induction m using consRecOn with
    | zero => rw [val_zero, addAux_nil]; exact CNFList.isCNFList _
    | cons f m k hm =>
      dsimp [cons_addAux_cons]
      split
      on_goal 3 => apply (expGT_addAux hl _ IH).isCNFList; simp_all
      all_goals exact (cons _ _ _ hm).isCNFList

/-- We define addition on `CNFList E` recursively, so that:

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

private theorem cons_add_cons' (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    (cons e n l hl + cons f k m hm).1 = match cmp e f with
      | .lt => (cons f k m hm).1
      | .eq => toLex (f, n + k) :: m.1
      | .gt => toLex (e, n) :: (l + cons f k m hm).1 :=
  rfl

theorem cons_add_cons (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl + cons f k m hm = match he : cmp e f with
      | .lt => cons f k m hm
      | .eq => cons f (n + k) m hm
      | .gt => cons e n (l + cons f k m hm) (expGT_add hl (by simpa using he)) := by
  rw [Subtype.eq_iff, cons_add_cons']
  aesop (add simp [lt_asymm])

theorem cons_add_cons_of_lt (he : e < f) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl + cons f k m hm = cons f k m hm := by
  rw [cons_add_cons]
  split <;> rename_i heq <;> rw [he.cmp_eq_lt] at heq <;> contradiction

theorem cons_add_cons_of_eq (he : e = f) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl + cons f k m hm = cons f (n + k) m hm := by
  rw [cons_add_cons]
  split <;> rename_i heq <;> rw [he.cmp_eq_eq] at heq <;> contradiction

theorem cons_add_cons_of_gt (he : f < e) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl + cons f k m hm =
      cons _ n (l + cons f k m hm) (expGT_add hl (by simpa using he)) := by
  rw [cons_add_cons]
  split <;> rename_i heq <;> rw [he.cmp_eq_gt] at heq <;> contradiction

@[simp]
theorem cons_add_cons_eq (hl : expGT e l) (n : ℕ+) (hm : expGT e m) (k : ℕ+) :
    cons e n l hl + cons e k m hm = cons e (n + k) m hm :=
  cons_add_cons_of_eq rfl ..

instance [Notation E] : LawfulAdd (CNFList E) where
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
          exact le_eval_cons hm _
        · rw [cons_add_cons_of_gt he, eval_cons]
          simp_rw [IH, eval_cons, add_assoc]

theorem cons_eq_add [Notation E] (hl : expGT e l) (n : ℕ+) : cons e n l hl = single e n + l := by
  rw [← eval_inj]; simp

end Add

/-! ### Subtraction -/

section Sub

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

private theorem cons_subAux_cons (a b : E ×ₗ ℕ+) (l m : List (E ×ₗ ℕ+)) :
    subAux (a :: l) (b :: m) = match cmp (ofLex a).1 (ofLex b).1 with
      | .lt => []
      | .eq =>
        match cmp (ofLex a).2 (ofLex b).2 with
        | .lt => []
        | .eq => subAux l m
        | .gt => toLex ((ofLex a).1, (ofLex a).2 - (ofLex b).2) :: l
      | .gt => a :: l :=
  rfl

private theorem isCNFList_subAux (l m : CNFList E) : IsCNFList (subAux l.1 m.1) := by
  induction l using consRecOn generalizing m with
  | zero => exact .nil
  | cons e n l hl IH =>
    cases m using consRecOn with
    | zero => rw [val_zero, subAux_nil]; exact CNFList.isCNFList _
    | cons f k m hm =>
      dsimp [cons_subAux_cons]
      have := fun n ↦ (cons e n l hl).isCNFList
      aesop

/-- We define subtraction on `CNFList E` recursively, so that:

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

private theorem cons_sub_cons' (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    (cons e n l hl - cons f k m hm).1 = match cmp e f with
      | .lt => []
      | .eq =>
        match cmp n k with
        | .lt => []
        | .eq => (l - m).1
        | .gt => toLex (e, n - k) :: l.1
      | .gt => (cons e n l hl).1 :=
  rfl

theorem cons_sub_cons (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl - cons f k m hm = match cmp e f with
      | .lt => 0
      | .eq =>
        match cmp n k with
        | .lt => 0
        | .eq => l - m
        | .gt => cons e (n - k) l hl
      | .gt => cons e n l hl := by
  rw [Subtype.eq_iff, cons_sub_cons']
  aesop

theorem cons_sub_cons_of_lt (he : e < f) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl - cons f k m hm = 0 := by
  rw [cons_sub_cons, he.cmp_eq_lt]

theorem cons_sub_cons_of_eq (he : e = f) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl - cons f k m hm = match cmp n k with
      | .lt => 0
      | .eq => l - m
      | .gt => cons e (n - k) l hl := by
  rw [cons_sub_cons, he.cmp_eq_eq]

theorem cons_sub_cons_of_gt (he : f < e) (hl : expGT e l) (n : ℕ+) (hm : expGT f m) (k : ℕ+) :
    cons e n l hl - cons f k m hm = cons e n l hl := by
  rw [cons_sub_cons, he.cmp_eq_gt]

theorem cons_sub_cons_eq_of_lt {n k : ℕ+} (hn : n < k) (hl : expGT e l) (hm : expGT e m) :
    cons e n l hl - cons e k m hm = 0 := by
  rw [cons_sub_cons_of_eq rfl, hn.cmp_eq_lt]

theorem cons_sub_cons_eq_of_eq {n k : ℕ+} (hn : n = k) (hl : expGT e l) (hm : expGT e m) :
    cons e n l hl - cons e k m hm = l - m := by
  rw [cons_sub_cons_of_eq rfl, hn.cmp_eq_eq]

theorem cons_sub_cons_eq_of_gt {n k : ℕ+} (hn : k < n) (hl : expGT e l) (hm : expGT e m) :
    cons e n l hl - cons e k m hm = cons e (n - k) l hl := by
  rw [cons_sub_cons_of_eq rfl, hn.cmp_eq_gt]

@[simp]
theorem cons_sub_cons_eq_eq (hl : expGT e l) (hm : expGT e m) (n : ℕ+) :
    cons e n l hl - cons e n m hm = l - m := by
  rw [cons_sub_cons_eq_of_eq rfl]

instance [Notation E] : LawfulSub (CNFList E) where
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

private theorem cons_mulAux_cons (a b : E ×ₗ ℕ+) (l m : List (E ×ₗ ℕ+)) :
    mulAux (a :: l) (b :: m) = if (ofLex b).1 = 0
      then toLex ((ofLex a).1, (ofLex a).2 * (ofLex b).2) :: l
      else toLex ((ofLex a).1 + (ofLex b).1, (ofLex b).2) :: mulAux (a :: l) m :=
  rfl

variable [LawfulAdd E]

private theorem expGT.cons_mulAux (hl : expGT e l) (hm : expGT f m) {n : ℕ+}
    (H : IsCNFList (mulAux (cons e n l hl).1 m.1)) : expGT (e + f) ⟨_, H⟩ := by
  induction m using consRecOn <;> aesop (add simp [mulAux_nil, cons_mulAux_cons])

private theorem isCNFList_mulAux (l m : CNFList E) : IsCNFList (mulAux l.1 m.1) := by
  induction l using consRecOn generalizing m with
  | zero => simp [nil_mulAux]
  | cons e n l hl IH =>
    induction m using consRecOn with
    | zero => simp [mulAux_nil]
    | cons f k m hm IH' =>
      dsimp [cons_mulAux_cons]
      split
      · exact hl.isCNFList n
      · exact (expGT.cons_mulAux _ hm _).isCNFList (l := ⟨_, IH'⟩) _

/-- We define multiplication on `CNFList E` recursively, so that:

* `0 * x` equals `x * 0` equals `0`.
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
theorem cons_mul_natCast (hl : expGT e l) (n k : ℕ+) : cons e n l hl * k = cons e (n * k) l hl := by
  rw [← single_zero, single_eq_cons, cons_mul_cons]; exact if_pos rfl

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
        · rw [cons_zero, cons_mul_natCast, eval_natCast]
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
          · simp [-eval_cons]
          · simpa

end Mul

end CNFList

/-! ### CNF-like types -/

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
  eval := equivList.toInitialSeg.transPrincipal eval

end CNFLike
end Ordinal.Notation
