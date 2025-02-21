import OrdinalNotation.CNFLike
import OrdinalNotation.Mathlib.Veblen
import Mathlib.Tactic.DeriveCountable

/-!
# Cantor normal form

But now using the `CNFLike` API, which should make this much easier!
-/

namespace Ordinal.Notation

open Ordinal Order Ordering

/-- Recursive definition of the Cantor normal form ordinal notation. `zero` denotes the ordinal `0`,
and `oadd e n a` is intended to refer to `ω ^ e * n + a`.

Comparison is performed lexicographically. We say that `ω ^ e * n + a` is a normal form
`PreCantor.NF` whenever `a < ω ^ e` and both `e` and `a` are normal forms. `Cantor` is the subtype
of normal forms. -/
inductive PreCantor : Type
  /-- The ordinal `0` -/
  | zero : PreCantor
  /-- The ordinal `oadd e n a = ω ^ e * n + a` -/
  | oadd : PreCantor → ℕ+ → PreCantor → PreCantor
  deriving Countable, DecidableEq

attribute [pp_nodot] PreCantor.oadd
compile_inductive% PreCantor

namespace PreCantor
variable {e a e₁ a₁ e₂ a₂ e₃ a₃ e₄ a₄ : PreCantor} {n₁ n₂ n₃ n₄ : ℕ+}

/-! ### Basic instances -/

theorem oadd_inj : oadd e₁ n₁ a₁ = oadd e₂ n₂ a₂ ↔ e₁ = e₂ ∧ n₁ = n₂ ∧ a₁ = a₂ :=
  propext_iff.1 <| oadd.injEq ..

/-- The ordinal `0` is represented as `zero`. -/
instance : Zero PreCantor := ⟨zero⟩
instance : Inhabited PreCantor := ⟨0⟩
@[simp] theorem zero_def : zero = 0 := rfl
attribute [nolint simpNF] zero.sizeOf_spec

theorem oadd_ne_zero : oadd e n a ≠ 0 := fun h ↦ by
  contradiction

/-- The ordinal `1` is represented as `oadd 0 1 0 = ω ^ 0 * 1 + 0`. -/
instance : One PreCantor := ⟨oadd 0 1 0⟩
@[simp] theorem one_def : oadd 0 1 0 = 1 := rfl
instance : NeZero (1 : PreCantor) := ⟨oadd_ne_zero⟩

/-- The ordinal `ω` is represented as `oadd 1 1 0 = ω ^ 1 * 1 + 0`. -/
instance : Omega PreCantor := ⟨oadd 1 1 0⟩

/-- The ordinal denoted by a notation.

This operation is non-computable, as is ordinal arithmetic in general, but it can be used to state
correctness results. -/
noncomputable def eval : PreCantor → Ordinal.{0}
  | 0 => 0
  | oadd e n a => ω ^ eval e * n + eval a

@[simp] theorem eval_zero : eval 0 = 0 := rfl
@[simp] theorem eval_one : eval 1 = 1 := by simp [eval]
@[simp] theorem eval_oadd (e n a) : eval (oadd e n a) = ω ^ eval e * n + eval a := rfl
@[simp] theorem eval_omega : eval omega = ω := by simp [omega]
theorem eval_oadd_one_zero (e) : eval (oadd e 1 0) = ω ^ eval e := by simp
theorem eval_oadd_nat_zero (e n) : eval (oadd e n 0) = ω ^ eval e * n := by simp

private theorem omega0_opow_pos {o : Ordinal} : 0 < ω ^ o :=
  opow_pos o omega0_pos

theorem snd_le_eval_oadd (e n a) : ω ^ eval e * n ≤ eval (oadd e n a) :=
  le_add_right _ _

theorem fst_le_eval_oadd (e n a) : ω ^ eval e ≤ eval (oadd e n a) :=
  (Ordinal.le_mul_left _ (mod_cast n.pos)).trans (snd_le_eval_oadd _ _ _)

theorem eval_oadd_pos : 0 < eval (oadd e n a) :=
  omega0_opow_pos.trans_le <| fst_le_eval_oadd e n a

theorem eval_oadd_ne_zero : eval (oadd e n a) ≠ 0 :=
  eval_oadd_pos.ne'

@[simp]
theorem eval_eq_zero {x : PreCantor} : eval x = 0 ↔ x = 0 := by
  cases x
  · simp
  · simpa using eval_oadd_ne_zero

theorem eval_lt_epsilon0 : ∀ x : PreCantor, eval x < ε₀
  | zero => epsilon_pos 0
  | oadd e n a => by
    apply principal_add_epsilon 0 (principal_mul_epsilon 0 (principal_opow_epsilon 0 _ _) _) _
    · exact omega0_lt_epsilon 0
    · exact eval_lt_epsilon0 e
    · exact nat_lt_epsilon n 0
    · exact eval_lt_epsilon0 a

/-- Casts a natural number into a `PreCantor` -/
instance : NatCast PreCantor where
  natCast
  | 0 => 0
  | Nat.succ n => oadd 0 n.succPNat 0

@[simp] theorem natCast_zero : (0 : ℕ) = (0 : PreCantor) := rfl
@[simp] theorem natCast_succ (n : ℕ) : n.succ = oadd 0 n.succPNat 0 := rfl
theorem natCast_one : (1 : ℕ) = (1 : PreCantor) := rfl

theorem oadd_zero_pNat_zero (n : ℕ+) : oadd 0 n 0 = n := by
  rw [← n.succPNat_natPred]
  rfl

@[simp] theorem eval_natCast (n : ℕ) : eval n = n := by cases n <;> simp

@[simp] theorem eval_ofNat (n : ℕ) [n.AtLeastTwo] :
    eval (no_index (OfNat.ofNat n)) = n :=
  eval_natCast n

theorem injective_natCast : Function.Injective (NatCast.natCast (R := PreCantor)) := by
  intro m n h
  apply_fun eval at h
  simpa using h

@[simp]
theorem natCast_inj (m n : ℕ) : (m : PreCantor) = n ↔ m = n :=
  injective_natCast.eq_iff

instance : Infinite PreCantor :=
  Infinite.of_injective _ injective_natCast

/-- Print `ω ^ s * n`, omitting `s` if `e = 0` or `e = 1`, and omitting `n` if `n = 1` -/
private def toStringAux (e : PreCantor) (n : ℕ) (s : String) : String :=
  if e = 0 then toString n
  else (if e = 1 then "ω" else "ω ^ (" ++ s ++ ")") ++ if n = 1 then "" else " * " ++ toString n

/-- Pretty-print a term in `PreCantor` -/
private def toString : PreCantor → String
  | zero => "0"
  | oadd e n 0 => toStringAux e n (toString e)
  | oadd e n a => toStringAux e n (toString e) ++ " + " ++ toString a

instance : ToString PreCantor :=
  ⟨toString⟩

open Lean in
/-- Print a term in `PreCantor` -/
private def repr' (prec : ℕ) : PreCantor → Format
  | zero => "0"
  | oadd e n a =>
    Repr.addAppParen
      ("oadd " ++ (repr' max_prec e) ++ " " ++ repr n ++ " " ++ (repr' max_prec a))
      prec

instance : Repr PreCantor where
  reprPrec o prec := repr' prec o

/-! ### Ordering -/

-- Most of this section is privated as the resulting linear order instance subsumes
-- almost everything else.
section cmp

/-- Comparison of `PreCantor` is performed lexicographically.

`ω ^ e₁ * n₁ + a₁` is less than `ω ^ e₂ * n₂ + a₂` when either `e₁ < e₂`, or `e₁ = e₂` and
`n₁ < n₂`, or `e₁ = e₂`, `n₁ = n₂`, and `a₁ < a₂`.

This forms a linear order, though not a well-founded one, as there's an infinite decreasing chain
`ω`, `0 + ω`, `0 + 0 + ω`, etc. Note however that the restriction of this order to normal forms is
a well-order. -/
protected def cmp : PreCantor → PreCantor → Ordering
  | 0, 0 => eq
  | 0, _ => lt
  | _, 0 => gt
  | (oadd e₁ n₁ a₁), (oadd e₂ n₂ a₂) => (e₁.cmp e₂).then ((_root_.cmp n₁ n₂).then (a₁.cmp a₂))

instance : LT PreCantor where lt x y := x.cmp y = lt
theorem lt_def (x y : PreCantor) : x < y ↔ x.cmp y = lt := Iff.rfl

instance : LE PreCantor where le x y := x.cmp y ≠ gt
theorem le_def (x y : PreCantor) : x ≤ y ↔ x.cmp y ≠ gt := Iff.rfl

@[simp]
protected theorem zero_le (x : PreCantor) : 0 ≤ x := by
  cases x <;> simp [le_def, PreCantor.cmp]

instance : OrderBot PreCantor where
  bot := 0
  bot_le := PreCantor.zero_le

@[simp]
protected theorem bot_eq_zero : (⊥ : PreCantor) = 0 :=
  rfl

theorem oadd_pos : 0 < oadd e n a := rfl

@[simp]
protected theorem not_lt_zero (x : PreCantor) : ¬ x < 0 := by
  cases x <;> simp [lt_def, PreCantor.cmp]

@[simp]
protected theorem le_zero {x : PreCantor} : x ≤ 0 ↔ x = 0 := by
  cases x <;> simp [le_def, PreCantor.cmp]

protected theorem zero_lt_one : (0 : PreCantor) < 1 := rfl

private theorem cmp_eq_eq_iff : ∀ {x y : PreCantor}, x.cmp y = eq ↔ x = y
  | 0, 0 | 0, oadd _ _ _ | oadd _ _ _, 0 => by simp [PreCantor.cmp]
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ => by
    simp_rw [PreCantor.cmp, then_eq_eq, cmp_eq_eq_iff, _root_.cmp_eq_eq_iff, oadd_inj]

private theorem cmp_self_eq_eq (x : PreCantor) : x.cmp x = eq :=
  cmp_eq_eq_iff.2 rfl

private theorem le_refl (x : PreCantor) : x ≤ x := by
  rw [le_def, x.cmp_self_eq_eq]
  decide

private theorem cmp_swap : ∀ x y : PreCantor, (x.cmp y).swap = y.cmp x
  | 0, 0 => rfl
  | 0, oadd _ _ _ => rfl
  | oadd _ _ _, 0 => rfl
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂ => by simp_rw [PreCantor.cmp, swap_then, cmp_swap, _root_.cmp_swap]

private theorem le_antisymm {x y : PreCantor} : x ≤ y → y ≤ x → x = y := by
  rw [le_def, le_def, ← x.cmp_swap, ← cmp_eq_eq_iff]
  generalize x.cmp y = a
  cases a <;> decide

private theorem le_trans : ∀ {x y z : PreCantor}, x ≤ y → y ≤ z → x ≤ z
  | 0, _, _, _, _ => PreCantor.zero_le _
  | oadd _ _ _, 0, _, h, _ | _, oadd _ _ _, 0, _, h => by rw [PreCantor.le_zero] at h; contradiction
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, oadd e₃ n₃ a₃, h₁, h₂ => by
    simp only [le_def, PreCantor.cmp, ne_eq, then_eq_gt, not_or, not_and, cmp_eq_eq_iff,
      _root_.cmp_eq_eq_iff, cmp_eq_gt_iff, not_lt] at h₁ h₂ ⊢
    simp_rw [← le_def] at h₁ h₂ ⊢
    use le_trans h₁.1 h₂.1
    rintro rfl
    have H := le_antisymm h₁.1 h₂.1
    replace h₁ := h₁.2 H
    replace h₂ := h₂.2 H.symm
    use h₁.1.trans h₂.1
    rintro rfl
    have H := h₁.1.antisymm h₂.1
    exact le_trans (h₁.2 H) (h₂.2 H.symm)

private theorem lt_iff_le_not_le (x y : PreCantor) : x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  rw [lt_def, le_def, le_def, ← x.cmp_swap]
  generalize x.cmp y = a
  cases a <;> decide

instance : Preorder PreCantor where
  le_refl := le_refl
  le_trans := @le_trans
  lt_iff_le_not_le := lt_iff_le_not_le

private theorem cmp_compares (x y : PreCantor) : (x.cmp y).Compares x y :=
  match h : x.cmp y with
  | lt => h
  | eq => by rwa [cmp_eq_eq_iff] at h
  | gt => by rw [compares_gt, gt_iff_lt, lt_def, ← x.cmp_swap, h]; rfl

instance : LinearOrder PreCantor :=
  linearOrderOfCompares PreCantor.cmp PreCantor.cmp_compares

@[simp]
theorem cmp_eq_cmp : PreCantor.cmp = cmp :=
  funext₂ fun a b ↦ (cmp_compares a b).cmp_eq.symm

theorem oadd_cmp_oadd (e₁ n₁ a₁ e₂ n₂ a₂) : cmp (oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) =
    (cmp e₁ e₂).then ((cmp n₁ n₂).then (cmp a₁ a₂)) := by
  rw [← cmp_eq_cmp]
  rfl

theorem oadd_lt_oadd : oadd e₁ n₁ a₁ < oadd e₂ n₂ a₂ ↔
    e₁ < e₂ ∨ e₁ = e₂ ∧ (n₁ < n₂ ∨ n₁ = n₂ ∧ a₁ < a₂) := by
  rw [← cmp_eq_lt_iff, oadd_cmp_oadd]
  simp [then_eq_lt]

theorem oadd_lt_oadd_fst (h : e₁ < e₂) : oadd e₁ n₁ a₁ < oadd e₂ n₂ a₂ := by
  rw [oadd_lt_oadd]
  exact Or.inl h

theorem oadd_lt_oadd_snd (h : n₁ < n₂) : oadd e n₁ a₁ < oadd e n₂ a₂ := by
  rw [oadd_lt_oadd]
  exact Or.inr ⟨rfl, Or.inl h⟩

theorem oadd_lt_oadd_thd (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂ := by
  rw [oadd_lt_oadd]
  exact Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩

theorem lt_oadd_self (e n a) : e < oadd e n a :=
  match e with
  | 0 => oadd_pos
  | oadd e n a => oadd_lt_oadd_fst (lt_oadd_self e n a)

theorem oadd_le_oadd : oadd e₁ n₁ a₁ ≤ oadd e₂ n₂ a₂ ↔
    e₁ < e₂ ∨ e₁ = e₂ ∧ (n₁ < n₂ ∨ n₁ = n₂ ∧ a₁ ≤ a₂) := by
  simp_rw [le_iff_lt_or_eq, oadd_lt_oadd, oadd_inj]
  tauto

theorem oadd_le_oadd_thd (h : a₁ ≤ a₂) : oadd e n a₁ ≤ oadd e n a₂ := by
  rw [oadd_le_oadd]
  exact Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩

@[simp]
protected theorem lt_one_iff_zero {x : PreCantor} : x < 1 ↔ x = 0 := by
  obtain (_ | ⟨e, n, a⟩) := x
  · simpa using PreCantor.zero_lt_one
  · rw [← one_def, oadd_lt_oadd]
    simp

end cmp

/-! ### Normal forms -/

/-- A normal form `PreCantor` has the form `ω ^ e₁ * n₁ + ω ^ e₂ * n₂ + ⋯ + ω ^ eₖ * nₖ` where
`e₁ > e₂ > ⋯ > eₖ` and all the `eᵢ` are also in normal form.

We will essentially only be interested in normal forms, but to avoid complicating the algorithms, we
define everything over `PreCantor` and only prove correctness with normal form as an invariant. -/
inductive NF : PreCantor → Prop
  /-- Zero is a normal form. -/
  | zero : NF 0
  /-- `ω ^ e * n + a` is a normal form when `e` and `a` are normal forms with `a < ω ^ e`. -/
  | oadd' {e a} : NF e → (n : ℕ+) → NF a → a < oadd e 1 0 → NF (oadd e n a)

@[nolint defLemma]
protected alias NF.oadd := NF.oadd'

theorem NF_oadd_iff : NF (oadd e n a) ↔ NF e ∧ NF a ∧ a < oadd e 1 0 := by
  refine ⟨?_, fun ⟨he, ha, h⟩ ↦ he.oadd n ha h⟩
  rintro ⟨⟩
  refine ⟨?_, ?_, ?_⟩
  assumption'

private def decidable_NF : DecidablePred NF := fun x ↦
  match x with
  | 0 => Decidable.isTrue NF.zero
  | oadd e n a => by
    refine @decidable_of_iff _ _ NF_oadd_iff.symm ?_
    letI := decidable_NF e
    letI := decidable_NF a
    infer_instance

instance : DecidablePred NF :=
  decidable_NF

theorem NF.fst (h : NF (oadd e n a)) : NF e := by
  rw [NF_oadd_iff] at h
  exact h.1

theorem NF.snd (h : NF (oadd e n a)) : NF a := by
  rw [NF_oadd_iff] at h
  exact h.2.1

theorem NF.lt_oadd (h : NF (oadd e n a)) : a < oadd e 1 0 := by
  rw [NF_oadd_iff] at h
  exact h.2.2

theorem NF.of_le (hx : NF (oadd e n a)) (ha : NF a') (h : a' ≤ a) : NF (oadd e n a') :=
  hx.fst.oadd n ha (h.trans_lt hx.lt_oadd)

theorem NF.oadd_zero (h : NF e) {n : ℕ+} : NF (oadd e n 0) :=
  h.oadd n NF.zero oadd_pos

theorem NF.zero_of_zero (h : NF (oadd 0 n a)) : a = 0 := by
  simpa using h.lt_oadd

theorem NF.with_nat (h : NF (oadd e n a)) (n') : NF (oadd e n' a) := by
  rwa [NF_oadd_iff] at h ⊢

theorem NF_natCast (n : ℕ) : NF n := by
  cases n
  · exact NF.zero
  · exact NF.oadd_zero NF.zero

theorem NF_one : NF 1 :=
  NF_natCast 1

theorem NF_oadd_iterate : ∀ n : ℕ, NF ((oadd · 1 0)^[n] 0)
  | 0 => NF.zero
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact (NF_oadd_iterate n).oadd _ NF.zero oadd_pos

theorem NF_omega : NF omega :=
  NF_oadd_iterate 2

theorem eval_lt_eval_of_lt : ∀ {x y}, NF x → NF y → x < y → eval x < eval y
  | _, 0, _, _, h => by simp at h
  | 0, oadd e n a, _, _, _ => eval_oadd_pos
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, hx, hy, h => by
    rw [oadd_lt_oadd] at h
    have H : eval (oadd e₁ n₁ a₁) < ω ^ e₁.eval * (n₁ + 1 : ℕ+) := by
      simpa [mul_succ] using eval_lt_eval_of_lt hx.snd hx.fst.oadd_zero hx.lt_oadd
    obtain he | ⟨rfl, hn | ⟨rfl, ha⟩⟩ := h
    · calc
        _ < ω ^ e₁.eval * (n₁ + 1 : ℕ+) := H
        _ < ω ^ succ e₁.eval := omega0_opow_mul_nat_lt (lt_succ _) _
        _ ≤ ω ^ e₂.eval := opow_le_opow_right omega0_pos
          (eval_lt_eval_of_lt hx.fst hy.fst he).succ_le
        _ ≤ eval (oadd e₂ n₂ a₂) := fst_le_eval_oadd e₂ n₂ a₂
    · calc
        _ < ω ^ e₁.eval * (n₁ + 1 : ℕ+) := H
        _ ≤ ω ^ eval e₁ * n₂ := (Ordinal.mul_le_mul_iff_left omega0_opow_pos).2
          (mod_cast Nat.succ_le.2 hn)
        _ ≤ eval (oadd e₁ n₂ a₂) := snd_le_eval_oadd e₁ n₂ a₂
    · exact (add_lt_add_iff_left _).2 (eval_lt_eval_of_lt hx.snd hy.snd ha)

theorem eval_le_eval_of_le {x y} (hx : NF x) (hy : NF y) (h : x ≤ y) : eval x ≤ eval y := by
  obtain h | rfl := h.lt_or_eq
  · exact (eval_lt_eval_of_lt hx hy h).le
  · rfl

theorem eval_lt_eval_iff {x y} (hx : NF x) (hy : NF y) : eval x < eval y ↔ x < y := by
  obtain h | rfl | h := lt_trichotomy x y
  · simp_rw [h, eval_lt_eval_of_lt hx hy h]
  · simp
  · simp_rw [h.not_lt, (eval_lt_eval_of_lt hy hx h).not_lt]

theorem eval_le_eval_iff {x y} (hx : NF x) (hy : NF y) : eval x ≤ eval y ↔ x ≤ y := by
  rw [← not_lt, ← not_lt, eval_lt_eval_iff hy hx]

theorem eval_inj {x y} (hx : NF x) (hy : NF y) : eval x = eval y ↔ x = y := by
  rw [le_antisymm_iff, le_antisymm_iff, eval_le_eval_iff hx hy, eval_le_eval_iff hy hx]

theorem NF.eval_lt_oadd (hx : NF (oadd e n a)) : eval a < ω ^ eval e := by
  simpa [eval_oadd] using eval_lt_eval_of_lt hx.snd hx.fst.oadd_zero hx.lt_oadd

theorem NF.add_absorp_mul (hx : NF (oadd e n a)) : eval a + ω ^ eval e * n = ω ^ eval e * n :=
  Ordinal.add_absorp hx.eval_lt_oadd (Ordinal.le_mul_left _ (mod_cast n.pos))

theorem NF.add_absorp (hx : NF (oadd e n a)) : eval a + ω ^ eval e = ω ^ eval e := by
  simpa using (hx.with_nat 1).add_absorp_mul

theorem NF.eval_oadd_lt_snd (hx : NF (oadd e n a)) {m} (hn : n < m) :
    eval (oadd e n a) < ω ^ eval e * m := by
  have : (n + 1 : Ordinal) ≤ m := mod_cast Nat.succ_le_of_lt hn
  apply lt_of_lt_of_le _ ((Ordinal.mul_le_mul_iff_left omega0_opow_pos).2 this)
  simpa [eval_oadd, mul_succ] using eval_lt_eval_of_lt hx.snd hx.fst.oadd_zero hx.lt_oadd

theorem NF.eval_oadd_lt_fst (hx : NF (oadd e n a)) {o} (he : eval e < o) :
    eval (oadd e n a) < ω ^ o :=
  (hx.eval_oadd_lt_snd n.lt_succ_self).trans <| omega0_opow_mul_nat_lt he _

theorem exists_NF_of_lt_epsilon0 {o} : o < ε₀ → ∃ x, NF x ∧ eval x = o := by
  obtain rfl | h0 := eq_or_ne o 0
  · exact fun _ ↦ ⟨0, NF.zero, rfl⟩
  · intro ho
    have He := log_omega0_lt_of_lt_epsilon0 h0 ho
    have Hn := div_opow_log_pos ω h0
    have Ha := mod_opow_log_lt_self ω h0
    obtain ⟨e, he, he'⟩ := exists_NF_of_lt_epsilon0 (He.trans ho)
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt o one_lt_omega0)
    obtain ⟨a, ha, ha'⟩ := exists_NF_of_lt_epsilon0 (Ha.trans ho)
    rw [hn] at Hn
    use oadd e ⟨n, mod_cast Hn⟩ a
    constructor
    · apply he.oadd _ ha
      rw [← eval_lt_eval_iff ha he.oadd_zero, ha', eval_oadd_one_zero, he']
      exact mod_lt _ (opow_ne_zero _ omega0_ne_zero)
    · rw [eval_oadd, he', PNat.mk_coe, ← hn, ha']
      exact Ordinal.div_add_mod _ _
termination_by o

end PreCantor

def Cantor := Subtype PreCantor.NF
  deriving LinearOrder, DecidableEq

namespace Cantor
open PreCantor Notation

theorem NF (x : Cantor) : NF x.1 := x.2
@[ext] theorem ext {x y : Cantor} (h : x.1 = y.1) : x = y := Subtype.ext h

/-- Construct a `Cantor` from an ordinal notation (and infer normality) -/
def mk (o : PreCantor) (h : o.NF := by decide) : Cantor := ⟨o, h⟩
@[simp] theorem mk_val (o h) : (mk o h).1 = o := rfl

/-- The `oadd` pseudo-constructor for `Cantor` -/
def oadd (e : Cantor) (n : ℕ+) (a : Cantor) (h : a.1 < oadd e.1 1 0 := by decide) : Cantor :=
  ⟨_, NF.oadd e.2 n a.2 h⟩

@[simp]
theorem val_oadd (e n a h) : (oadd e n a h).val = PreCantor.oadd e.1 n a.1 :=
  rfl

instance : Zero Cantor := ⟨⟨_, NF.zero⟩⟩
instance : One Cantor := ⟨⟨_, NF_one⟩⟩
instance : Omega Cantor := ⟨⟨_, NF_omega⟩⟩
instance : Inhabited Cantor := ⟨0⟩

@[simp] theorem val_zero : (0 : Cantor).val = 0 := rfl
@[simp] theorem val_one : (1 : Cantor).val = 1 := rfl
@[simp] theorem val_omega : (omega : Cantor).val = omega := rfl

instance : ToString Cantor :=
  ⟨fun x => x.1.toString⟩

instance : Repr Cantor :=
  ⟨fun x prec => x.1.repr' prec⟩

/-- This is a recursor-like theorem for `Cantor` suggesting an inductive definition, which can't
actually be defined this way due to conflicting dependencies. -/
@[elab_as_elim]
def recOn {C : Cantor → Sort*} (o : Cantor) (H0 : C 0)
    (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) : C o := by
  cases' o with o h
  induction' o with e n a IHe IHa
  · exact H0
  · exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.lt_oadd (IHe _) (IHa _)

@[simp]
theorem recOn_zero {C : Cantor → Sort*} (H0 : C 0)
    (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) : recOn 0 H0 H1 = H0 :=
  rfl

@[simp]
theorem recOn_oadd {C : Cantor → Sort*} (e n a h) (H0 : C 0)
    (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) :
    recOn (oadd e n a h) H0 H1 = H1 e n a h (recOn e H0 H1) (recOn a H0 H1) :=
  rfl

private noncomputable def eval : Cantor <i Ordinal.{0} where
  toFun x := x.1.eval
  inj' x y h := by simpa [← Subtype.eq_iff] using (PreCantor.eval_inj x.2 y.2).1 h
  map_rel_iff' {x y} := by simpa using PreCantor.eval_lt_eval_iff x.2 y.2
  top := ε₀
  mem_range_iff_rel' x := by
    constructor
    · rintro ⟨x, rfl⟩
      exact eval_lt_epsilon0 _
    · intro ho
      obtain ⟨x, hx, rfl⟩ := exists_NF_of_lt_epsilon0 ho
      exact ⟨⟨x, hx⟩, rfl⟩

instance instNotation : Notation Cantor := by
  apply ofEval eval <;> simp [eval]

private def equivListFun (x : Cantor) : CNFList Cantor :=
  x.recOn 0 fun e n _ _ _ IH ↦ ⟨toLex (e, n) :: IH.1, sorry⟩

private def equivListSymm (x : CNFList Cantor) : Cantor :=
  x.consRecOn 0 fun e n _ _ IH ↦ ⟨PreCantor.oadd e.1 n IH.1, sorry⟩

private def equivList : Cantor ≃o CNFList Cantor where
  toFun := equivListFun
  invFun := equivListSymm
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry

instance : CNFLike Cantor where
  Exp := Cantor
  equivList := equivList
  equivList_zero := sorry
  equivList_one := sorry
  equivList_omega := sorry

instance : NatCast Cantor := inferInstance
instance : NatCast (Exp Cantor) := instNatCast
instance : LawfulNatCast Cantor := inferInstance
instance : LawfulNatCast (Exp Cantor) := instLawfulNatCast
instance : Add Cantor := inferInstance
instance : Add (Exp Cantor) := instAdd
instance : LawfulAdd Cantor := inferInstance
instance : LawfulAdd (Exp Cantor) := instLawfulAdd
instance : Sub Cantor := inferInstance
instance : Sub (Exp Cantor) := instSub
instance : LawfulSub Cantor := inferInstance
instance : LawfulSub (Exp Cantor) := instLawfulSub
instance : Mul Cantor := inferInstance
instance : Mul (Exp Cantor) := instMul
instance : LawfulMul Cantor := inferInstance
instance : LawfulMul (Exp Cantor) := instLawfulMul
instance : Div Cantor := inferInstance
instance : Div (Exp Cantor) := instDiv
instance : LawfulDiv Cantor := inferInstance
instance : LawfulDiv (Exp Cantor) := instLawfulDiv
instance : Split Cantor := inferInstance
instance : Split (Exp Cantor) := instSplit
instance : Pow Cantor Cantor := CNFLike.instPow
instance : LawfulPow Cantor Cantor :=  CNFLike.instLawfulPow

noncomputable instance : ConditionallyCompleteLinearOrderBot Cantor :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

#eval! toString <| ((omega * 2 : Cantor) ^ (omega + 1 : Cantor))

end Cantor

end Ordinal.Notation
