/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
-/
import Mathlib.Data.Ordering.Lemmas
import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.NormNum
import OrdinalNotation.ForMathlib
import OrdinalNotation.FundamentalSequence

/-!
# Ordinal notation

Constructive ordinal arithmetic for ordinals below `ε₀`.

We define a type `PreCantor`, with constructors `0 : PreCantor` and `PreCantor.oadd e n a`
representing `ω ^ e * n + a`.

We say that `o` is in normal form `PreCantor.NF o` if either `o = 0` or `o = ω ^ e * n + a` with
`a < ω ^ e` for `e` and `a` in normal form.

The type `Cantor` is the type of ordinals below `ε₀` in normal form.
Various operations (addition, subtraction, multiplication, exponentiation) are defined on `Cantor`.

## Vi's addendum

This file would not exist if not for Mario's work. That being said, this file has been heavily
modified from the Mathlib original, to fix what I percieve to be various weaknesses.

- `ONote` is renamed to `PreCantor` and `NONote` is renamed to `Cantor`.
- The `Preorder` instance is no longer defined in terms of `repr`, thus making it computable.
- `NFBelow` is disposed of, and `NF` is no longer a typeclass.
- The definition of `opow` is heavily simplified, avoiding multiple auxiliary definitions and
  instead relying only on `natOpow`.
- Most proofs are golfed substantially by relying on new lemmas for ordinal arithmetic (in
  particular, I got rid of those hideous `simp only says`).
-/

open Ordinal Order Ordering

/-- Recursive definition of the Cantor normal form ordinal notation. `zero` denotes the ordinal `0`,
and `oadd e n a` is intended to refer to `ω ^ e * n + a`.

Comparison is performed lexicographically. We say that `ω ^ e * n + a` is a normal form
`PreCantor.NF` whenever `a < ω ^ e` and both `e` and `a` are normal forms.

For this to be a valid Cantor normal form, we must have the exponents decrease to the right, but we
can't state this condition until we've defined the ordering, so we make it a separate definition
`NF`. -/
inductive PreCantor : Type
  /-- The ordinal `0` -/
  | zero : PreCantor
  /-- The ordinal `oadd e n a = ω ^ e * n + a` -/
  | oadd : PreCantor → ℕ+ → PreCantor → PreCantor
  deriving DecidableEq

attribute [pp_nodot] PreCantor.oadd

compile_inductive% PreCantor

namespace PreCantor

variable {e a e₁ a₁ e₂ a₂ e₃ a₃ e₄ a₄ : PreCantor} {n₁ n₂ n₃ n₄ : ℕ+}

/-! ### Basic instances -/

theorem oadd_inj : oadd e₁ n₁ a₁ = oadd e₂ n₂ a₂ ↔ e₁ = e₂ ∧ n₁ = n₂ ∧ a₁ = a₂ :=
  oadd.injEq .. ▸ Iff.rfl

/-- The ordinal `0` is represented as `zero`. -/
instance : Zero PreCantor :=
  ⟨zero⟩

attribute [nolint simpNF] zero.sizeOf_spec

@[simp]
theorem zero_def : zero = 0 :=
  rfl

instance : Inhabited PreCantor :=
  ⟨0⟩

theorem oadd_ne_zero : oadd e n a ≠ 0 := fun h ↦ by
  contradiction

/-- The ordinal `1` is represented as `oadd 0 1 0 = ω ^ 0 * 1 + 0`. -/
instance : One PreCantor :=
  ⟨oadd 0 1 0⟩

@[simp]
theorem one_def : oadd 0 1 0 = 1 :=
  rfl

/-- The ordinal `ω` is represented as `oadd 1 1 0 = ω ^ 1 * 1 + 0`. -/
def omega : PreCantor :=
  oadd 1 1 0

/-- The ordinal denoted by a notation.

This operation is non-computable, as is ordinal arithmetic in general, but it can be used to state
correctness results. -/
noncomputable def repr : PreCantor → Ordinal.{0}
  | 0 => 0
  | oadd e n a => ω ^ repr e * n + repr a

@[simp] theorem repr_zero : repr 0 = 0 := rfl
@[simp] theorem repr_one : repr 1 = 1 := by simp [repr]
@[simp] theorem repr_oadd (e n a) : repr (oadd e n a) = ω ^ repr e * n + repr a := rfl
theorem repr_oadd_one_zero (e) : repr (oadd e 1 0) = ω ^ repr e := by simp
theorem repr_oadd_nat_zero (e n) : repr (oadd e n 0) = ω ^ repr e * n := by simp

private theorem omega0_opow_pos {o : Ordinal} : 0 < ω ^ o :=
  opow_pos o omega0_pos

theorem snd_le_repr_oadd (e n a) : ω ^ repr e * n ≤ repr (oadd e n a) :=
  le_add_right _ _

theorem fst_le_repr_oadd (e n a) : ω ^ repr e ≤ repr (oadd e n a) :=
  (Ordinal.le_mul_left _ (mod_cast n.pos)).trans (snd_le_repr_oadd _ _ _)

theorem repr_oadd_pos : 0 < repr (oadd e n a) :=
  omega0_opow_pos.trans_le <| fst_le_repr_oadd e n a

theorem repr_oadd_ne_zero : repr (oadd e n a) ≠ 0 :=
  repr_oadd_pos.ne'

@[simp]
theorem repr_eq_zero {x : PreCantor} : repr x = 0 ↔ x = 0 := by
  cases x
  · simp
  · simpa using repr_oadd_ne_zero

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

@[simp] theorem repr_natCast (n : ℕ) : repr n = n := by cases n <;> simp

@[simp] theorem repr_ofNat (n : ℕ) [n.AtLeastTwo] :
    repr (no_index (OfNat.ofNat n)) = n :=
  repr_natCast n

/-- Print `ω ^ s * n`, omitting `s` if `e = 0` or `e = 1`, and omitting `n` if `n = 1` -/
private def toString_aux (e : PreCantor) (n : ℕ) (s : String) : String :=
  if e = 0 then toString n
  else (if e = 1 then "ω" else "ω ^ (" ++ s ++ ")") ++ if n = 1 then "" else " * " ++ toString n

/-- Pretty-print an ordinal notation -/
private def toString : PreCantor → String
  | zero => "0"
  | oadd e n 0 => toString_aux e n (toString e)
  | oadd e n a => toString_aux e n (toString e) ++ " + " ++ toString a

instance : ToString PreCantor :=
  ⟨toString⟩

open Lean in
/-- Print an ordinal notation -/
private def repr' (prec : ℕ) : PreCantor → Format
  | zero => "0"
  | oadd e n a =>
    Repr.addAppParen
      ("oadd " ++ (repr' max_prec e) ++ " " ++ Nat.repr (n : ℕ) ++ " " ++ (repr' max_prec a))
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

instance : LT PreCantor where
  lt x y := x.cmp y = lt

theorem lt_def (x y : PreCantor) : x < y ↔ x.cmp y = lt := Iff.rfl

instance : LE PreCantor where
  le x y := x.cmp y ≠ gt

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

theorem oadd_pos (e n a) : 0 < oadd e n a := rfl

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
  | 0 => oadd_pos 0 n a
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
  h.oadd n NF.zero (oadd_pos e n 0)

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
    exact (NF_oadd_iterate n).oadd _ NF.zero (oadd_pos _ _ _)

theorem NF_omega : NF omega :=
  NF_oadd_iterate 2

theorem repr_lt_repr_of_lt : ∀ {x y}, NF x → NF y → x < y → repr x < repr y
  | _, 0, _, _, h => by simp at h
  | 0, oadd e n a, _, _, _ => repr_oadd_pos
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, hx, hy, h => by
    rw [oadd_lt_oadd] at h
    have H : repr (oadd e₁ n₁ a₁) < ω ^ e₁.repr * (n₁ + 1 : ℕ+) := by
      simpa [mul_succ] using repr_lt_repr_of_lt hx.snd hx.fst.oadd_zero hx.lt_oadd
    obtain he | ⟨rfl, hn | ⟨rfl, ha⟩⟩ := h
    · calc
        _ < ω ^ e₁.repr * (n₁ + 1 : ℕ+) := H
        _ < ω ^ succ e₁.repr := omega0_opow_mul_nat_lt (lt_succ _) _
        _ ≤ ω ^ e₂.repr := opow_le_opow_right omega0_pos
          (repr_lt_repr_of_lt hx.fst hy.fst he).succ_le
        _ ≤ repr (oadd e₂ n₂ a₂) := fst_le_repr_oadd e₂ n₂ a₂
    · calc
        _ < ω ^ e₁.repr * (n₁ + 1 : ℕ+) := H
        _ ≤ ω ^ repr e₁ * n₂ := (Ordinal.mul_le_mul_iff_left omega0_opow_pos).2
          (mod_cast Nat.succ_le.2 hn)
        _ ≤ repr (oadd e₁ n₂ a₂) := snd_le_repr_oadd e₁ n₂ a₂
    · exact (add_lt_add_iff_left _).2 (repr_lt_repr_of_lt hx.snd hy.snd ha)

theorem repr_le_repr_of_le {x y} (hx : NF x) (hy : NF y) (h : x ≤ y) : repr x ≤ repr y := by
  obtain h | rfl := h.lt_or_eq
  · exact (repr_lt_repr_of_lt hx hy h).le
  · rfl

theorem repr_lt_repr_iff {x y} (hx : NF x) (hy : NF y) : repr x < repr y ↔ x < y := by
  obtain h | rfl | h := lt_trichotomy x y
  · simp_rw [h, repr_lt_repr_of_lt hx hy h]
  · simp
  · simp_rw [h.not_lt, (repr_lt_repr_of_lt hy hx h).not_lt]

theorem repr_le_repr_iff {x y} (hx : NF x) (hy : NF y) : repr x ≤ repr y ↔ x ≤ y := by
  rw [← not_lt, ← not_lt, repr_lt_repr_iff hy hx]

theorem repr_inj {x y} (hx : NF x) (hy : NF y) : repr x = repr y ↔ x = y := by
  rw [le_antisymm_iff, le_antisymm_iff, repr_le_repr_iff hx hy, repr_le_repr_iff hy hx]

theorem NF.repr_lt_oadd (hx : NF (oadd e n a)) : repr a < ω ^ repr e := by
  simpa [repr_oadd] using repr_lt_repr_of_lt hx.snd hx.fst.oadd_zero hx.lt_oadd

theorem NF.add_absorp_mul (hx : NF (oadd e n a)) : repr a + ω ^ repr e * n = ω ^ repr e * n :=
  Ordinal.add_absorp hx.repr_lt_oadd (Ordinal.le_mul_left _ (mod_cast n.pos))

theorem NF.add_absorp (hx : NF (oadd e n a)) : repr a + ω ^ repr e = ω ^ repr e := by
  simpa using (hx.with_nat 1).add_absorp_mul

theorem NF.repr_oadd_lt_snd (hx : NF (oadd e n a)) {m} (hn : n < m) :
    repr (oadd e n a) < ω ^ repr e * m := by
  have : (n + 1 : Ordinal) ≤ m := mod_cast Nat.succ_le_of_lt hn
  apply lt_of_lt_of_le _ ((Ordinal.mul_le_mul_iff_left omega0_opow_pos).2 this)
  simpa [repr_oadd, mul_succ] using repr_lt_repr_of_lt hx.snd hx.fst.oadd_zero hx.lt_oadd

theorem NF.repr_oadd_lt_fst (hx : NF (oadd e n a)) {o} (he : repr e < o) :
    repr (oadd e n a) < ω ^ o :=
  (hx.repr_oadd_lt_snd n.lt_succ_self).trans <| omega0_opow_mul_nat_lt he _

/-! ### Addition -/

/-- Addition of Cantor normal forms (correct only for normal input) -/
def add : PreCantor → PreCantor → PreCantor
  | 0, x | x, 0 => x
  | oadd e₁ n₁ a₁, x₂@(oadd e₂ n₂ a₂) =>
    match cmp e₁ e₂ with
    | lt => x₂
    | eq => oadd e₁ (n₁ + n₂) a₂
    | gt => oadd e₁ n₁ (add a₁ x₂)

instance : AddZeroClass PreCantor where
  add := add
  zero := 0
  zero_add x := by cases x <;> rfl
  add_zero x := by cases x <;> rfl

@[simp]
theorem add_def (x y : PreCantor) : add x y = x + y :=
  rfl

theorem oadd_add_oadd_of_lt (h : e₁ < e₂) : oadd e₁ n₁ a₁ + oadd e₂ n₂ a₂ = oadd e₂ n₂ a₂ := by
  rw [← add_def, add, h.cmp_eq_lt]

@[simp]
theorem oadd_add_oadd_of_eq : oadd e n₁ a₁ + oadd e n₂ a₂ = oadd e (n₁ + n₂) a₂ := by
  rw [← add_def, add, _root_.cmp_self_eq_eq]

theorem oadd_add_oadd_of_gt (h : e₂ < e₁) :
    oadd e₁ n₁ a₁ + oadd e₂ n₂ a₂ = oadd e₁ n₁ (a₁ + oadd e₂ n₂ a₂) := by
  rw [← add_def, add, h.cmp_eq_gt, add_def]

theorem repr_add : ∀ {x y}, NF x → NF y → repr (x + y) = repr x + repr y
  | 0, x, _, _ | x, 0, _, _ => by simp
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, hx, hy => by
    obtain h | rfl | h := lt_trichotomy e₁ e₂
    · rw [oadd_add_oadd_of_lt h]
      exact (add_absorp (hx.repr_oadd_lt_fst (repr_lt_repr_of_lt hx.fst hy.fst h))
        (fst_le_repr_oadd _ _ _)).symm
    · rw [oadd_add_oadd_of_eq, repr_oadd, repr_oadd, PNat.add_coe, Nat.cast_add, mul_add,
        add_assoc, add_assoc, add_left_cancel]
      exact (add_absorp hx.repr_lt_oadd (fst_le_repr_oadd _ _ _)).symm
    · rw [oadd_add_oadd_of_gt h, repr_oadd, repr_add hx.snd hy]
      simp [add_assoc]

theorem NF.add : ∀ {x y}, NF x → NF y → NF (x + y)
  | 0, x, _, _ | x, 0, _, _ => by simpa
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, hx, hy => by
    obtain h | rfl | h := lt_trichotomy e₁ e₂
    · rwa [oadd_add_oadd_of_lt h]
    · rw [oadd_add_oadd_of_eq]
      exact hy.with_nat _
    · rw [oadd_add_oadd_of_gt h, NF_oadd_iff]
      use hx.fst, hx.snd.add hy
      rw [← repr_lt_repr_iff (hx.snd.add hy) hx.fst.oadd_zero, repr_add hx.snd hy]
      simpa [repr_oadd] using principal_add_omega0_opow _ hx.repr_lt_oadd
        (hy.repr_oadd_lt_fst (repr_lt_repr_of_lt hy.fst hx.fst h))

/-! ### Subtraction -/

/-- Subtraction of Cantor normal forms (correct only for normal input) -/
def sub : PreCantor → PreCantor → PreCantor
  | 0, _ => 0
  | x, 0 => x
  | x₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    match cmp e₁ e₂ with
    | lt => 0
    | gt => x₁
    | eq =>
      match cmp n₁ n₂ with
      | lt => 0
      | eq => sub a₁ a₂
      | gt => oadd e₁ (n₁ - n₂) a₁

instance : Sub PreCantor :=
  ⟨sub⟩

@[simp]
theorem sub_def (x y : PreCantor) : sub x y = x - y :=
  rfl

@[simp]
theorem zero_sub (x : PreCantor) : 0 - x = 0 := by
  cases x <;> rfl

@[simp]
theorem sub_zero (x : PreCantor) : x - 0 = x := by
  cases x <;> rfl

theorem oadd_sub_oadd_of_lt (h : e₁ < e₂) : oadd e₁ n₁ a₁ - oadd e₂ n₂ a₂ = 0 := by
  rw [← sub_def, sub, h.cmp_eq_lt]

theorem oadd_sub_oadd_of_gt (h : e₂ < e₁) :
    oadd e₁ n₁ a₁ - oadd e₂ n₂ a₂ = oadd e₁ n₁ a₁ := by
  rw [← sub_def, sub, h.cmp_eq_gt]

theorem oadd_sub_oadd_of_eq_of_lt (h : n₁ < n₂) : oadd e n₁ a₁ - oadd e n₂ a₂ = 0 := by
  rw [← sub_def, sub, _root_.cmp_self_eq_eq, h.cmp_eq_lt]

@[simp]
theorem oadd_sub_oadd_of_eq_of_eq : oadd e n a₁ - oadd e n a₂ = a₁ - a₂ := by
  rw [← sub_def, sub, _root_.cmp_self_eq_eq, _root_.cmp_self_eq_eq, sub_def]

theorem oadd_sub_oadd_of_eq_of_gt (h : n₂ < n₁) :
    oadd e n₁ a₁ - oadd e n₂ a₂ = oadd e (n₁ - n₂) a₁ := by
  rw [← sub_def, sub, _root_.cmp_self_eq_eq, h.cmp_eq_gt]

theorem repr_sub : ∀ {x y}, NF x → NF y → repr (x - y) = repr x - repr y
  | 0, _, _, _ | _, 0, _, _ => by simp
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, hx, hy => by
    obtain he | rfl | he := lt_trichotomy e₁ e₂
    · rw [oadd_sub_oadd_of_lt he, repr_zero, eq_comm, Ordinal.sub_eq_zero_iff_le,
        repr_le_repr_iff hx hy]
      exact (oadd_lt_oadd_fst he).le
    · obtain hn | rfl | hn := lt_trichotomy n₁ n₂
      · rw [oadd_sub_oadd_of_eq_of_lt hn, repr_zero, eq_comm, Ordinal.sub_eq_zero_iff_le,
          repr_le_repr_iff hx hy]
        exact (oadd_lt_oadd_snd hn).le
      · rw [oadd_sub_oadd_of_eq_of_eq, repr_oadd, repr_oadd, add_sub_add_cancel,
          repr_sub hx.snd hy.snd]
      · rw [oadd_sub_oadd_of_eq_of_gt hn]
        apply (sub_eq_of_add_eq _).symm
        rw [← repr_add hy (hx.with_nat _), oadd_add_oadd_of_eq, PNat.add_sub_of_lt hn]
    · rw [oadd_sub_oadd_of_gt he]
      apply (sub_eq_of_add_eq _).symm
      rw [← repr_add hy hx, oadd_add_oadd_of_lt he]

theorem NF.sub : ∀ {x y}, NF x → NF y → NF (x - y)
  | 0, _, _, _ | _, 0, _, _ => by simpa
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, hx, hy => by
    obtain he | rfl | he := lt_trichotomy e₁ e₂
    · rw [oadd_sub_oadd_of_lt he]
      exact NF.zero
    · obtain hn | rfl | hn := lt_trichotomy n₁ n₂
      · rw [oadd_sub_oadd_of_eq_of_lt hn]
        exact NF.zero
      · rw [oadd_sub_oadd_of_eq_of_eq]
        exact hx.snd.sub hy.snd
      · rw [oadd_sub_oadd_of_eq_of_gt hn]
        exact hx.with_nat _
    · rwa [oadd_sub_oadd_of_gt he]

/-! ### Multiplication -/

/-- Multiplication of ordinal notations (correct only for normal input) -/
def mul : PreCantor → PreCantor → PreCantor
  | 0, _ => 0
  | _, 0 => 0
  | oadd e₁ n₁ a₁, oadd 0 n₂ _ => oadd e₁ (n₁ * n₂) a₁
  | x₁@(oadd e₁ _ _), oadd e₂ n₂ a₂ => oadd (e₁ + e₂) n₂ (mul x₁ a₂)

instance : MulZeroClass PreCantor where
  mul := mul
  zero := 0
  zero_mul x := by cases x <;> rfl
  mul_zero x := by cases x <;> rfl

@[simp]
theorem mul_def (x y : PreCantor) : mul x y = x * y :=
  rfl

@[simp]
theorem oadd_mul_oadd_zero : oadd e₁ n₁ a₁ * oadd 0 n₂ a₂ = oadd e₁ (n₁ * n₂) a₁ :=
  rfl

@[simp]
theorem oadd_mul_pNat {n' : ℕ+} : oadd e n a * n' = oadd e (n * n') a := by
  rw [← oadd_zero_pNat_zero, oadd_mul_oadd_zero]

theorem oadd_mul_oadd_oadd : oadd e₁ n₁ a₁ * oadd (oadd e₃ n₃ a₃) n₂ a₂ =
    oadd (e₁ + oadd e₃ n₃ a₃) n₂ (oadd e₁ n₁ a₁ * a₂) :=
  rfl

private theorem pNat_eq_succ (n : ℕ+) : n = succ (n.natPred : Ordinal) := by
  rw [← add_one_eq_succ, ← Nat.cast_add_one, n.natPred_add_one]

theorem repr_mul : ∀ {x y}, NF x → NF y → repr (x * y) = repr x * repr y
  | 0, x, _, _ | x, 0, _, _ => by simp
  | oadd e₁ n₁ a₁, oadd 0 n₂ _, hx, hy => by
    obtain rfl := hy.zero_of_zero
    simp_rw [oadd_mul_oadd_zero, oadd_zero_pNat_zero, repr_natCast, repr_oadd,
      pNat_eq_succ n₂, add_mul_succ _ hx.add_absorp_mul, ← pNat_eq_succ, mul_assoc,
      PNat.mul_coe, natCast_mul]
  | oadd e₁ n₁ a₁, oadd (oadd e₃ n₃ a₃) n₂ a₂, hx, hy => by
    simp_rw [oadd_mul_oadd_oadd, repr_oadd, mul_add, repr_mul hx hy.snd, repr_oadd]
    congr 1
    rw [← mul_assoc, mul_natCast_add_mul_of_isLimit hx.add_absorp _ n₁.pos,
      repr_add hx.fst hy.fst, opow_add, repr_oadd, mul_assoc]
    exact isLimit_omega0_opow repr_oadd_pos.ne'

theorem NF.mul : ∀ {x y}, NF x → NF y → NF (x * y)
  | 0, x, _, _ | x, 0, _, _ => by simpa
  | oadd e₁ n₁ a₁, oadd 0 n₂ _, hx, _ => by
    rw [oadd_mul_oadd_zero]
    exact hx.with_nat _
  | oadd e₁ n₁ a₁, oadd (oadd e₃ n₃ a₃) n₂ a₂, hx, hy => by
    rw [oadd_mul_oadd_oadd, NF_oadd_iff]
    have H := hx.mul hy.snd
    use hx.fst.add hy.fst, H
    rw [← repr_lt_repr_iff H (hx.fst.add hy.fst).oadd_zero, repr_mul hx hy.snd,
      repr_oadd, repr_oadd, PNat.val_ofNat, Nat.cast_one, mul_one, repr_zero, add_zero]
    apply ((mul_lt_mul_iff_left repr_oadd_pos).2 hy.repr_lt_oadd).trans_le
    rw [repr_add hx.fst hy.fst, opow_add, repr_oadd,
      mul_natCast_add_mul_of_isLimit hx.add_absorp (isLimit_omega0_opow repr_oadd_pos.ne') n₁.pos]

/-! ### Exponentiation -/

/-- Evaluates `n ^ x` for `n : ℕ+` (correct only for normal input) -/
def natOpow (n : ℕ+) (x : PreCantor) : PreCantor :=
  if n = 1 then 1 else
    match x with
    | 0 => 1
    | oadd 0 m _ => Nat.pow n m
    | oadd (oadd 0 n₂ _) n₁ a => oadd (oadd n₂.natPred n₁ 0) 1 0 * natOpow n a
    | oadd e@(oadd (oadd _ _ _) _ _) n₁ a => oadd (oadd e n₁ 0) 1 0 * natOpow n a

theorem one_natOpow (x : PreCantor) : natOpow 1 x = 1 := by
  rw [natOpow.eq_def, if_pos rfl]

theorem natOpow_zero (n : ℕ+) : natOpow n 0 = 1 := by
  rw [natOpow.eq_def]
  split <;> rfl

theorem NF.natOpow {n : ℕ+} {x : PreCantor} (hx : NF x) : NF (natOpow n x) := by
  obtain rfl | hn := eq_or_ne n 1
  · rw [one_natOpow]
    exact NF_one
  · rw [natOpow.eq_def, if_neg hn]
    split
    · exact NF_one
    · exact NF_natCast _
    · exact (NF_natCast _).oadd_zero.oadd_zero.mul hx.snd.natOpow
    · exact hx.fst.oadd_zero.oadd_zero.mul hx.snd.natOpow

theorem repr_natOpow (n : ℕ+) {x : PreCantor} (hx : NF x) :
    repr (natOpow n x) = n ^ repr x := by
  obtain rfl | hn := n.one_le.eq_or_lt
  · simp [one_natOpow]
  · rw [natOpow.eq_def, if_neg hn.ne']
    change 1 < (n : ℕ) at hn
    split
    · simp
    · obtain rfl := hx.zero_of_zero
      simp
    · obtain rfl := hx.fst.zero_of_zero
      rename_i n₁ a₁ n₂ a₂
      rw [repr_mul (NF_natCast _).oadd_zero.oadd_zero hx.snd.natOpow, repr_natOpow _ hx.snd]
      suffices ω ^ ω ^ a₁.natPred = ((n : Ordinal.{0}) ^ ω ^ (a₁ : ℕ)) by
        simp [opow_add, opow_mul, this]
      rw [← a₁.natPred_add_one, natCast_opow_omega0_opow_succ hn]
    · rw [repr_mul hx.fst.oadd_zero.oadd_zero hx.snd.natOpow, repr_natOpow _ hx.snd, repr_oadd,
        ← natCast_opow_omega0 hn, ← opow_mul, repr_oadd, mul_add, ← mul_assoc, ← opow_one_add,
        repr_oadd, ← add_assoc, one_add_omega0_opow_mul repr_oadd_pos.ne' (mod_cast PNat.ne_zero _)]
      simp [opow_add, opow_mul]

/-- Exponentiation of ordinal notations (correct only for normal input) -/
def opow : PreCantor → PreCantor → PreCantor
  | _, 0 => 1
  | 0, _ => 0
  | oadd 0 n _, x => natOpow n x
  | x@(oadd (oadd _ _ _) _ _), oadd 0 n _ => npowRec n x
  | x@(oadd e₁@(oadd _ _ _) _ _), oadd e₂ n₂ a₂ => oadd (e₁ * oadd e₂ n₂ 0) 1 0 * opow x a₂

instance : Pow PreCantor PreCantor :=
  ⟨opow⟩

@[simp]
theorem opow_def (x y : PreCantor) : opow x y = x ^ y :=
  rfl

@[simp]
theorem opow_zero (x : PreCantor) : x ^ (0 : PreCantor) = 1 := by
  rw [← opow_def, opow.eq_def]
  split <;> first | rfl | contradiction

@[simp]
theorem zero_opow_oadd (e n a) : (0 : PreCantor) ^ oadd e n a = 0 :=
  rfl

/-- This variant of `one_opow` does not assume the LHS is the normalized form for `1`. -/
@[simp]
theorem one_opow' (x : PreCantor) : (oadd 0 1 a) ^ x = 1 := by
  rw [← opow_def, opow.eq_def]
  split
  pick_goal 3
  · convert ← one_natOpow _
    rename_i h h'
    rw [oadd_inj] at h
    exact h.2.1
  all_goals simp at *

@[simp]
theorem one_opow (x : PreCantor) : (1 : PreCantor) ^ x = 1 :=
  one_opow' x

@[simp]
theorem natOpow_def (n : ℕ+) (x : PreCantor) : natOpow n x = n ^ x := by
  rw [← opow_def, opow.eq_def, ← oadd_zero_pNat_zero]
  split
  pick_goal 3
  · rename_i h h'
    rw [oadd_inj] at h
    rw [h.2.1]
  all_goals simp [natOpow_zero] at *

theorem opow_oadd₄ : (oadd (oadd e₁ n₂ a₂) n₁ a₁) ^ oadd (oadd e₂ n₄ a₄) n₃ a₃ =
    oadd (oadd e₁ n₂ a₂ * oadd (oadd e₂ n₄ a₄) n₃ 0) 1 0 * oadd (oadd e₁ n₂ a₂) n₁ a₁ ^ a₃ := by
  rw [← opow_def, opow.eq_def]
  split
  pick_goal 5
  · rename_i h₁ h₂
    simp_rw [oadd_inj] at h₁ h₂
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₂
    rfl
  all_goals simp at *

theorem NF.npowRec (hx : NF x) : ∀ n : ℕ, NF (npowRec n x)
  | 0 => NF_one
  | n + 1 => (hx.npowRec n).mul hx

theorem repr_npowRec (hx : NF x) : ∀ n : ℕ, repr (_root_.npowRec n x) = repr x ^ n
  | 0 => repr_one
  | n + 1 => by
    rw [pow_succ, ← repr_npowRec hx]
    exact repr_mul (hx.npowRec n) hx

theorem NF.opow : ∀ {x y}, NF x → NF y → NF (x ^ y)
  | _, 0, _, _ => by rw [opow_zero]; exact NF_one
  | 0, oadd _ _ _, _, _ => NF.zero
  | oadd 0 n _, x, hy, hx => by
    rw [hy.zero_of_zero, oadd_zero_pNat_zero, ← natOpow_def]
    exact hx.natOpow
  | (oadd (oadd _ _ _) _ _), oadd 0 n _, hx, _ => hx.npowRec n
  | (oadd (oadd e₁ n₂ a₂) n₁ a₁), oadd (oadd e₂ n₄ a₄) n₃ a₃, hx, hy => by
    rw [opow_oadd₄]
    exact (hx.fst.mul hy.fst.oadd_zero).oadd_zero.mul (hx.opow hy.snd)

theorem repr_oadd_opow (h : NF (oadd e n a)) (he : e ≠ 0)
    {o : Ordinal} (ho : IsLimit o) : repr (oadd e n a) ^ o = ω ^ (repr e * o) := by
  apply _root_.le_antisymm
  · apply (opow_le_opow_left _ (h.repr_oadd_lt_fst (lt_succ _)).le).trans_eq
    rw [← opow_mul, succ_mul_of_isLimit _ ho]
    rwa [ne_eq, repr_eq_zero]
  · rw [opow_mul]
    exact (opow_le_opow_left _ (fst_le_repr_oadd e n a))

theorem repr_oadd_opow_repr_oadd (hx : NF (oadd e₁ n₁ a₁)) (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) :
    repr (oadd e₁ n₁ a₁) ^ repr (oadd e₂ n₂ a₂) = ω ^ (repr e₁ * repr (oadd e₂ n₂ 0))
      * repr (oadd e₁ n₁ a₁) ^ repr a₂ := by
  rw [repr_oadd e₂, opow_add, repr_oadd_opow hx he₁]
  · simp
  · apply isLimit_mul_left (isLimit_opow_left isLimit_omega0 _) (mod_cast n₂.pos)
    rwa [ne_eq, repr_eq_zero]

theorem repr_opow : ∀ {x y}, NF x → NF y → repr (x ^ y) = repr x ^ repr y
  | _, 0, _, _ => by simp
  | 0, oadd _ _ _, _, _ => by
    rw [zero_opow_oadd, repr_zero, repr_oadd, zero_opow]
    exact repr_oadd_ne_zero
  | oadd 0 n _, x, hy, hx => by
    rw [hy.zero_of_zero, oadd_zero_pNat_zero, ← natOpow_def, repr_natCast, repr_natOpow _ hx]
  | (oadd (oadd _ _ _) _ _), oadd 0 n _, hx, hy => by
    obtain rfl := hy.zero_of_zero
    apply (repr_npowRec hx _).trans
    simp
  | (oadd (oadd e₁ n₂ a₂) n₁ a₁), oadd (oadd e₂ n₄ a₄) n₃ a₃, hx, hy => by
    rw [opow_oadd₄, repr_oadd_opow_repr_oadd hx oadd_ne_zero oadd_ne_zero,
      repr_mul (hx.fst.mul hy.fst.oadd_zero).oadd_zero (hx.opow hy.snd), repr_opow hx hy.snd,
      repr_oadd, repr_mul hx.fst hy.fst.oadd_zero]
    simp

end PreCantor

/- ### Type of normal forms -/

/-- The type of Cantor normal forms is the subtype of `PreCantor` with the `PreCantor.NF`
property. -/
def Cantor : Type :=
  { x : PreCantor // x.NF }

namespace Cantor

instance : DecidableEq Cantor :=
  inferInstanceAs (DecidableEq (Subtype _))

open PreCantor

theorem NF (x : Cantor) : NF x.1 :=
  x.2

@[ext]
theorem ext {x y : Cantor} (h : x.1 = y.1) : x = y :=
  Subtype.ext h

/-- Construct a `Cantor` from an ordinal notation (and infer normality) -/
def mk (o : PreCantor) (h : o.NF := by decide) : Cantor :=
  ⟨o, h⟩

@[simp]
theorem mk_val (o h) : (mk o h).1 = o :=
  rfl

/-- The `oadd` pseudo-constructor for `Cantor` -/
def oadd (e : Cantor) (n : ℕ+) (a : Cantor) (h : a.1 < oadd e.1 1 0 := by decide) : Cantor :=
  ⟨_, NF.oadd e.2 n a.2 h⟩

instance : Zero Cantor :=
  ⟨⟨0, NF.zero⟩⟩

instance : Inhabited Cantor :=
  ⟨0⟩

@[simp]
theorem val_zero : (0 : Cantor).val = 0 :=
  rfl

@[simp]
theorem mk_zero : ⟨0, NF.zero⟩ = (0 : Cantor) :=
  rfl

instance : One Cantor :=
  ⟨⟨1, NF_one⟩⟩

/-- The ordinal `ω` is represented as `oadd 1 1 0 = ω ^ 1 * 1 + 0`. -/
def omega : Cantor :=
  oadd 1 1 0

instance : NatCast Cantor where
  natCast n := ⟨n, NF_natCast n⟩

instance : ToString Cantor :=
  ⟨fun x => x.1.toString⟩

instance : Repr Cantor :=
  ⟨fun x prec => x.1.repr' prec⟩

instance : LinearOrder Cantor :=
  Subtype.instLinearOrder _

instance : OrderBot Cantor :=
  Subtype.orderBot NF.zero

@[simp]
protected theorem bot_eq_zero : (⊥ : Cantor) = 0 :=
  rfl

@[simp]
protected theorem zero_le (x : Cantor) : 0 ≤ x :=
  x.1.zero_le

/-- The ordinal represented by an ordinal notation.

This function is noncomputable because ordinal arithmetic is noncomputable. In computational
applications `Cantor` can be used exclusively without reference to `Ordinal`, but this function
allows for correctness results to be stated. -/
noncomputable def repr : Cantor <i Ordinal where
  toFun x := x.1.repr
  inj' x y h := ext <| (PreCantor.repr_inj x.2 y.2).1 h
  map_rel_iff' {x y} := PreCantor.repr_lt_repr_iff x.2 y.2
  top := sorry -- TODO: this is ε₀
  mem_range_iff_rel' := sorry

theorem repr_val (x : Cantor) : repr x = x.1.repr :=
  rfl

@[simp]
theorem repr_zero : repr 0 = 0 :=
  PreCantor.repr_zero

@[simp]
theorem repr_one : repr 1 = 1 :=
  PreCantor.repr_one

@[simp]
theorem repr_natCast (n : ℕ) : repr n = n :=
  PreCantor.repr_natCast n

@[simp]
theorem repr_ofNat (n : ℕ) [n.AtLeastTwo] : repr (no_index (OfNat.ofNat n)) = n :=
  repr_natCast n

theorem repr_lt_repr_iff {x y : Cantor} : repr x < repr y ↔ x < y :=
  repr.lt_iff_lt

theorem repr_le_repr_iff {x y : Cantor} : repr x ≤ repr y ↔ x ≤ y :=
  repr.le_iff_le

theorem repr_inj {x y : Cantor} : repr x = repr y ↔ x = y :=
  repr.inj

theorem mem_range_repr_of_le {o : Ordinal} {x : Cantor} (h : o ≤ repr x) : o ∈ Set.range repr :=
  repr.mem_range_of_le h

theorem lt_wf : @WellFounded Cantor (· < ·) :=
  repr.wellFounded wellFounded_lt

instance : WellFoundedLT Cantor :=
  ⟨lt_wf⟩

instance : WellFoundedRelation Cantor :=
  ⟨(· < ·), lt_wf⟩

-- TODO: this can be deleted soon
instance : IsWellOrder Cantor (· < ·) where

/-- Cantor normal forms form a conditionally complete order, but note that this is non-constructive
as there's no way to decide in finite time the supremum/infimum of an infinite set. -/
noncomputable instance : ConditionallyCompleteLinearOrderBot Cantor :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

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

/-- Addition of Cantor normal forms -/
instance : Add Cantor :=
  ⟨fun x y => ⟨_, x.2.add y.2⟩⟩

@[simp]
theorem repr_add (a b) : repr (a + b) = repr a + repr b :=
  PreCantor.repr_add a.2 b.2

/-- Subtraction of ordinal notations -/
instance : Sub Cantor :=
  ⟨fun x y => ⟨_, x.2.sub y.2⟩⟩

@[simp]
theorem repr_sub (a b) : repr (a - b) = repr a - repr b :=
  PreCantor.repr_sub a.2 b.2

/-- Multiplication of ordinal notations -/
instance : Mul Cantor :=
  ⟨fun x y => ⟨_, x.2.mul y.2⟩⟩

@[simp]
theorem repr_mul (a b) : repr (a * b) = repr a * repr b :=
  PreCantor.repr_mul a.2 b.2

/-- Exponentiation of ordinal notations -/
instance : Pow Cantor Cantor :=
  ⟨fun x y => ⟨_, x.2.opow y.2⟩⟩

@[simp]
theorem repr_opow (a b) : repr (a ^ b) = repr a ^ repr b :=
  PreCantor.repr_opow a.2 b.2

@[simp]
theorem repr_oadd (e n a h) : repr (oadd e n a h) = ω ^ repr e * n + repr a :=
  PreCantor.repr_oadd _ _ _

@[simp]
theorem repr_omega : repr omega = ω := by
  apply (repr_oadd _ _ _ _).trans
  simp

theorem oadd_eq (e n a h) : oadd e n a h = omega ^ e * n + a := by
  rw [← repr_inj]
  simp

instance : NoMaxOrder Cantor where
  exists_gt x := by
    use x + 1
    rw [← repr.lt_iff_lt, repr_add, repr_one]
    exact lt_succ (repr x)

instance : SuccOrder Cantor := by
  refine SuccOrder.ofCore (· + 1) ?_ ?_ <;> simp [← repr_le_repr_iff]

instance : SuccAddOrder Cantor :=
  ⟨fun _ ↦ rfl⟩

-- TODO: decidable instance for `IsLimit`

end Cantor

namespace PreCantor

theorem mem_range_repr_of_le {o} (hx : NF x) (h : o ≤ repr x) : ∃ y, NF y ∧ repr y = o := by
  change o ≤ Cantor.repr ⟨x, hx⟩ at h
  obtain ⟨y, hy⟩ := Cantor.mem_range_repr_of_le h
  exact ⟨y.1, y.2, hy⟩

/-! ### Fundamental sequences -/

open Sequence

/-- The Wainer hierarchy as a sequence in `PreCantor`. -/
def wainerSeq : PreCantor → Sequence PreCantor
  | 0 => ∅
  | oadd e n a =>
    match a with
    | oadd _ _ _ => (wainerSeq a).map (.oadd e n ·)
    | 0 =>
      let s₁ := wainerSeq e
      let s₂ : Sequence PreCantor := match s₁ with
        | Sum.inl none => {0}
        | Sum.inl (some x) => ofFun fun k ↦ oadd x k.succPNat 0
        | Sum.inr f => ofFun fun k ↦ oadd (f k) 1 0
      match n with
      | 1 => s₂
      | ⟨n + 2, _⟩ => s₂.map (oadd e n.succPNat ·)

@[simp] theorem wainerSeq_zero : wainerSeq 0 = ∅ := rfl
@[simp] theorem wainerSeq_one : wainerSeq 1 = {0} := rfl

theorem wainerSeq_oadd_oadd : wainerSeq (oadd e₁ n₁ (oadd e₂ n₂ a)) =
    (wainerSeq (oadd e₂ n₂ a)).map (oadd e₁ n₁ ·) :=
  rfl

theorem wainerSeq_oadd_zero {n : ℕ} (hn : 0 < n + 2) :
    wainerSeq (oadd e ⟨_, hn⟩ 0) = (wainerSeq (oadd e 1 0)).map (oadd e n.succPNat ·) :=
  rfl

@[simp]
theorem wainerSeq_eq_empty : ∀ {x}, wainerSeq x = ∅ ↔ x = 0
  | 0 => by simp
  | oadd e₁ n₁ (oadd e₂ n₂ a) => by
    rw [wainerSeq]
    simpa using wainerSeq_eq_empty.ne.2 oadd_ne_zero
  | oadd e₁ n₁ 0 => by
    rw [wainerSeq.eq_def]
    dsimp
    split <;> split <;> simp

theorem lt_of_mem_wainerSeq (hx : x ∈ wainerSeq y) : x < y := by
  match y with
  | 0 => contradiction
  | .oadd e n (.oadd _ _ _) =>
    rw [wainerSeq_oadd_oadd, mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact oadd_lt_oadd_thd (lt_of_mem_wainerSeq ha)
  | .oadd e 1 0 =>
    rw [wainerSeq.eq_def] at hx
    dsimp at hx
    split at hx
    · obtain rfl := hx
      exact oadd_pos _ _ _
    all_goals
      rename_i h
      obtain ⟨k, rfl⟩ := hx
      apply oadd_lt_oadd_fst (lt_of_mem_wainerSeq _)
      rw [h]
    · rfl
    · exact Set.mem_range_self k
  | .oadd e ⟨n + 2, _⟩ 0 =>
    rw [wainerSeq_oadd_zero, mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact oadd_lt_oadd_snd (Nat.lt_succ_self _)

theorem NF.wainerSeq (hx : x.NF) (hy : y ∈ wainerSeq x) : y.NF := by
  match x with
  | 0 => rw [wainerSeq_zero] at hy; contradiction
  | .oadd e n (oadd _ _ _) =>
    rw [wainerSeq_oadd_oadd, mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact hx.fst.oadd _ (NF.wainerSeq hx.snd ha) ((lt_of_mem_wainerSeq ha).trans hx.lt_oadd)
  | .oadd e n 0 =>
    have : ∀ {y}, y ∈ PreCantor.wainerSeq (.oadd e 1 0) → y.NF := by
      intro y hy
      rw [wainerSeq.eq_def] at hy
      dsimp at hy
      split at hy
      · obtain rfl := hy
        exact NF.zero
      all_goals
        rename_i h
        obtain ⟨k, rfl⟩ := hy
        apply (hx.fst.wainerSeq _).oadd_zero
        rw [h]
      · rfl
      · exact Set.mem_range_self k
    match n with
    | 1 => exact this hy
    | ⟨n + 2, _⟩ =>
      rw [wainerSeq_oadd_zero, mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      exact hx.fst.oadd _ (this ha) (lt_of_mem_wainerSeq ha)

theorem wainerSeq_strictMono : ∀ x : PreCantor, (wainerSeq x).StrictMono
  | 0 => ⟨⟩
  | .oadd e n (oadd _ _ _) => (wainerSeq_strictMono _).map fun x y ↦ oadd_lt_oadd_thd
  | .oadd e n 0 => by
    have : (wainerSeq (.oadd e 1 0)).StrictMono := by
      rw [wainerSeq.eq_def]
      dsimp
      split
      · trivial
      · exact fun x y h ↦ oadd_lt_oadd_snd <| Nat.succPNat_lt_succPNat.2 h
      · rename_i hf
        exact fun x y h ↦ oadd_lt_oadd_fst <| (hf ▸ wainerSeq_strictMono _) h
    match n with
    | 1 => exact this
    | ⟨n + 2, _⟩ =>
      rw [wainerSeq_oadd_zero]
      exact this.map fun x y ↦ oadd_lt_oadd_thd

private theorem lt_oadd (hx : NF e) (hy : NF y) (he : e ≠ 0) (h : y < oadd e 1 0) :
    ∃ e' n, NF e' ∧ e' < e ∧ y ≤ oadd e' n 0 := by
  rw [← repr_lt_repr_iff hy hx.oadd_zero, repr_oadd_one_zero, lt_omega0_opow] at h
  · obtain ⟨o, ho, n, hya⟩ := h
    obtain ⟨z, hz, rfl⟩ := mem_range_repr_of_le hx ho.le
    use z, n.succPNat, hz, (repr_lt_repr_iff hz hx).1 ho
    rw [← repr_le_repr_iff hy hz.oadd_zero, repr_oadd_nat_zero]
    exact hya.le.trans (mul_le_mul_left' (mod_cast n.le_succ) _)
  · rwa [ne_eq, repr_eq_zero]

private theorem lt_oadd_oadd (hx : NF (oadd e₁ n₁ (oadd e₂ n₂ a))) (hy : NF y)
    (h : y < oadd e₁ n₁ (oadd e₂ n₂ a)) : ∃ z, NF z ∧ z < oadd e₂ n₂ a ∧ y ≤ oadd e₁ n₁ z := by
  rw [← repr_lt_repr_iff hy hx, repr_oadd, lt_add_iff repr_oadd_ne_zero] at h
  obtain ⟨o, ho, hye⟩ := h
  obtain ⟨z, hz, rfl⟩ := mem_range_repr_of_le hx.snd ho.le
  replace ho := (repr_lt_repr_iff hz hx.snd).1 ho
  use z, hz, ho
  rwa [← repr_oadd, repr_le_repr_iff hy (hx.of_le hz ho.le)] at hye

private theorem lt_oadd_succ (hx : NF e) (hy : NF y) (h : y < oadd (e + 1) 1 0) :
    ∃ n : ℕ, y ≤ oadd e n.succPNat 0 := by
  rw [← repr_lt_repr_iff hy (hx.add NF_one).oadd_zero, repr_oadd_one_zero, repr_add hx NF_one,
    repr_one, add_one_eq_succ, lt_omega0_opow_succ] at h
  obtain ⟨n, h⟩ := h
  use n
  rw [← repr_le_repr_iff hy hx.oadd_zero, repr_oadd_nat_zero]
  exact h.le.trans (mul_le_mul_left' (mod_cast n.le_succ) _)

private theorem lt_oadd_zero (hx : NF e) (hy : NF y) {hn : 0 < n + 2} (h : y < oadd e ⟨_, hn⟩ 0) :
    ∃ a, NF a ∧ a < oadd e 1 0 ∧ y ≤ oadd e n.succPNat a := by
  have : ⟨n + 2, hn⟩ = n.succPNat + 1 := rfl
  rw [this, ← repr_lt_repr_iff hy hx.oadd_zero, repr_oadd_nat_zero, PNat.add_coe, PNat.val_ofNat,
    Nat.cast_add_one, mul_add_one, lt_add_iff omega0_opow_pos.ne'] at h
  obtain ⟨o, ho, hye⟩ := h
  have ho : o < Cantor.repr ⟨oadd e 1 0, hx.oadd_zero⟩ := by simpa [Cantor.repr_val]
  obtain ⟨z, hz, rfl⟩ := mem_range_repr_of_le hx.oadd_zero ho.le
  replace ho := (repr_lt_repr_iff hz hx.oadd_zero).1 ho
  use z, hz, ho
  rw [← repr_le_repr_iff hy (hx.oadd _ hz ho)]
  apply hye.trans
  simp [Cantor.repr_val]

theorem isLimit_wainerSeq (hx : NF x) (hy : NF y) : y < x ↔ ∃ z ∈ wainerSeq x, y ≤ z := by
  refine ⟨fun hyx ↦ ?_, fun ⟨z, hz, hy⟩ ↦ hy.trans_lt (lt_of_mem_wainerSeq hz)⟩
  match x with
  | 0 => cases PreCantor.not_lt_zero _ hyx
  | oadd e n (oadd _ _ _) =>
    rw [wainerSeq_oadd_oadd]
    obtain ⟨z, hz, hza, hyz⟩ := lt_oadd_oadd hx hy hyx
    obtain ⟨w, hw, hzw⟩ := (isLimit_wainerSeq hx.snd hz).1 hza
    simp_rw [mem_map, exists_exists_and_eq_and]
    exact ⟨w, hw, hyz.trans (oadd_le_oadd_thd hzw)⟩
  | oadd e n 0 =>
    replace hx := hx.fst
    have {y} (hy : NF y) (hyx : y < oadd e 1 0) : ∃ z ∈ wainerSeq (oadd e 1 0), y ≤ z := by
      rw [wainerSeq.eq_def]
      dsimp
      split
      · rename_i he
        obtain rfl := wainerSeq_eq_empty.1 he
        simpa using hyx
      · rename_i z he
        have hz : NF z := hx.wainerSeq (he ▸ rfl)
        have H := fun (y : Cantor) ↦ isLimit_wainerSeq hx y.2
        simp_rw [he, sum_inl_some_def, mem_singleton_iff, exists_eq_left] at H
        change ∀ y : Cantor, y < ⟨e, hx⟩ ↔ y ≤ ⟨z, hz⟩ at H
        obtain rfl := Subtype.eq_iff.1 (covBy_iff_lt_iff_le.2 H).add_one_eq
        simpa using lt_oadd_succ hz hy hyx
      · rename_i f he
        have he' : e ≠ 0 := by
          rw [ne_eq, ← wainerSeq_eq_empty, he]
          exact ofFun_ne_empty _
        obtain ⟨z, _, hz, hze, hyz⟩ := lt_oadd hx hy he' hyx
        obtain ⟨w, hw, hzw⟩ := (isLimit_wainerSeq hx hz).1 hze
        obtain ⟨n, rfl⟩ := he ▸ hw
        simp_rw [mem_ofFun_iff, Set.mem_range, exists_exists_eq_and]
        exact ⟨_, hyz.trans (oadd_lt_oadd_fst (hzw.trans_lt <| (he ▸ wainerSeq_strictMono e)
          n.lt_succ_self)).le⟩
    match n with
    | 1 => exact this hy hyx
    | ⟨n + 2, _⟩ =>
      rw [wainerSeq_oadd_zero]
      obtain ⟨z, hz, hze, hye⟩ := lt_oadd_zero hx hy hyx
      obtain ⟨w, hw, hzw⟩ := this hz hze
      simp_rw [mem_map, exists_exists_and_eq_and]
      exact ⟨w, hw, hye.trans (oadd_le_oadd_thd hzw)⟩

end PreCantor

namespace Cantor

open PreCantor

/-- The underlying sequence of the `wainer` hierarchy -/
def wainerSeq : Cantor → Sequence Cantor :=
  fun x ↦ (PreCantor.wainerSeq _).pmap fun _ hy ↦ ⟨_, x.2.wainerSeq hy⟩

theorem wainerSeq_ext {x y : Cantor} (h : x.1.wainerSeq = y.1.wainerSeq) :
    x.wainerSeq = y.wainerSeq := by
  suffices ∀ {x y : Sequence PreCantor} {hx : ∀ z ∈ x, _} {hy : ∀ z ∈ y, _}, x = y →
    (x.pmap fun a ha ↦ mk a (hx a ha)) = (y.pmap fun b hb ↦ mk b (hy b hb)) from this h
  rintro _ _ _ _ rfl
  rfl

@[simp] theorem wainerSeq_zero : wainerSeq 0 = ∅ := rfl
@[simp] theorem wainerSeq_one : wainerSeq 1 = {0} := rfl

theorem mem_wainerSeq {x y : Cantor} : x ∈ wainerSeq y ↔ x.1 ∈ y.1.wainerSeq := by
  rw [wainerSeq, Sequence.mem_pmap]
  refine ⟨?_, fun h ↦ ⟨x.1, h, rfl⟩⟩
  rintro ⟨a, h, rfl⟩
  exact h

theorem lt_of_mem_wainerSeq {x y : Cantor} (hx : x ∈ wainerSeq y) : x < y :=
  PreCantor.lt_of_mem_wainerSeq (mem_wainerSeq.1 hx)

theorem wainerSeq_strictMono (x : Cantor) : (wainerSeq x).StrictMono :=
  (PreCantor.wainerSeq_strictMono _).attach.map fun _ _ h ↦ h

theorem isLimit_wainerSeq (x : Cantor) : (wainerSeq x).IsLimit x := by
  refine @fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨z, hz, hyz⟩ := (PreCantor.isLimit_wainerSeq x.2 y.2).1 hy
    exact ⟨⟨z, x.2.wainerSeq hz⟩, mem_wainerSeq.2 hz, hyz⟩
  · rintro ⟨z, hz, hyz⟩
    exact hyz.trans_lt (lt_of_mem_wainerSeq hz)

theorem isFundamental_wainerSeq (x : Cantor) : (wainerSeq x).IsFundamental x :=
  ⟨wainerSeq_strictMono x, isLimit_wainerSeq x⟩

/-- The Wainer hierarchy is a fundamental sequence system for Cantor normal forms, defined as
follows:

* `(ω ^ e₁ + … + ω ^ eₖ)[n] = ω ^ e₁ + … + (ω ^ eₖ)[n]`
* `(ω ^ (e + 1))[n] = ω ^ e * (n + 1)`
* `(ω ^ e)[n] = ω ^ e[n]` for limit `e`
-/
def wainer : FundamentalSystem Cantor :=
  fun x ↦ ⟨_, isFundamental_wainerSeq x⟩

@[simp]
theorem wainer_val (x : Cantor) : (wainer x).1 = wainerSeq x :=
  rfl

/-- Extend the Wainer hierarchy to `ε₀` by defining its fundamental sequence as
`0`, `1`, `ω`, `ω ^ ω`, `ω ^ ω ^ ω`, … -/
def wainerWithTop : FundamentalSystem (WithTop Cantor) := by
  refine wainer.withTop (fun n ↦ ⟨_, NF_oadd_iterate n⟩) ?_ ?_
  · apply strictMono_nat_of_lt_succ
    simp_rw [Function.iterate_succ_apply']
    exact fun _ ↦ lt_oadd_self _ _ _
  · refine fun x ↦ recOn x ⟨0, le_rfl⟩ ?_
    rintro e n a h ⟨m, hm⟩ -
    use m + 2
    simp_rw [Function.iterate_succ_apply']
    exact (oadd_lt_oadd_fst <| (Subtype.mk_le_mk.1 hm).trans_lt (lt_oadd_self _ _ _)).le

-- TODO: change to `decide` once the sorries have been disposed of

@[simp]
theorem fastGrowing_top_zero : fastGrowing wainerWithTop ⊤ 0 = 1 := by
  native_decide

@[simp]
theorem fastGrowing_top_one : fastGrowing wainerWithTop ⊤ 1 = 2 := by
  native_decide

@[simp]
theorem fastGrowing_top_two : fastGrowing wainerWithTop ⊤ 2 = 2048 := by
  native_decide

end Cantor
