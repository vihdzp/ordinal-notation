/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Ordering.Lemmas
import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.NormNum

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
- The definition of `add` is simplified.
-/

open Ordinal Order

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

compile_inductive% PreCantor

namespace PreCantor

variable {e a e₁ a₁ e₂ a₂ : PreCantor} {n₁ n₂ : ℕ+}

/-! ### Basic instances -/

theorem oadd_inj : oadd e₁ n₁ a₁ = oadd e₂ n₂ a₂ ↔ e₁ = e₂ ∧ n₁ = n₂ ∧ a₁ = a₂ :=
  oadd.injEq .. ▸ Iff.rfl

/-- The ordinal `0` is represented as `zero`. -/
instance : Zero PreCantor :=
  ⟨zero⟩

@[simp]
theorem zero_def : zero = 0 :=
  rfl

instance : Inhabited PreCantor :=
  ⟨0⟩

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

theorem repr_oadd (e n a) : repr (oadd e n a) = ω ^ repr e * n + repr a :=
  rfl

private theorem omega0_opow_pos {o : Ordinal} : 0 < ω ^ o :=
  opow_pos o omega0_pos

theorem snd_le_repr_oadd (e n a) : ω ^ repr e * n ≤ repr (oadd e n a) :=
  le_add_right _ _

theorem fst_le_repr_oadd (e n a) : ω ^ repr e ≤ repr (oadd e n a) :=
  (Ordinal.le_mul_left _ (mod_cast n.pos)).trans (snd_le_repr_oadd _ _ _)

theorem repr_oadd_pos (e n a) : 0 < repr (oadd e n a) :=
  omega0_opow_pos.trans_le <| fst_le_repr_oadd e n a

@[simp]
theorem repr_eq_zero {x : PreCantor} : repr x = 0 ↔ x = 0 := by
  cases x
  · simp
  · simpa using (repr_oadd_pos _ _ _).ne'

/-- Casts a natural number into a `PreCantor` -/
instance : NatCast PreCantor where
  natCast
  | 0 => 0
  | Nat.succ n => oadd 0 n.succPNat 0

@[simp] theorem natCast_zero : (0 : ℕ) = (0 : PreCantor) := rfl
@[simp] theorem natCast_succ (n : ℕ) : n.succ = oadd 0 n.succPNat 0 := rfl
@[simp] theorem natCast_one : (1 : ℕ) = (1 : PreCantor) := rfl

@[simp] theorem repr_natCast (n : ℕ) : repr n = n := by cases n <;> simp [repr_oadd]

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

open Ordering

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
  | Ordering.lt => h
  | Ordering.eq => by rwa [cmp_eq_eq_iff] at h
  | Ordering.gt => by rw [compares_gt, gt_iff_lt, lt_def, ← x.cmp_swap, h]; rfl

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

theorem oadd_le_oadd : oadd e₁ n₁ a₁ ≤ oadd e₂ n₂ a₂ ↔
    e₁ < e₂ ∨ e₁ = e₂ ∧ (n₁ < n₂ ∨ n₁ = n₂ ∧ a₁ ≤ a₂) := by
  simp_rw [le_iff_lt_or_eq, oadd_lt_oadd, oadd_inj]
  tauto

theorem oadd_lt_oadd_fst (h : e₁ < e₂) : oadd e₁ n₁ a₁ < oadd e₂ n₂ a₂ := by
  rw [oadd_lt_oadd]
  exact Or.inl h

theorem oadd_lt_oadd_snd (h : n₁ < n₂) : oadd e n₁ a₁ < oadd e n₂ a₂ := by
  rw [oadd_lt_oadd]
  exact Or.inr ⟨rfl, Or.inl h⟩

theorem oadd_lt_oadd_thd (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂ := by
  rw [oadd_lt_oadd]
  exact Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩

@[simp]
protected theorem lt_one_iff_zero {x : PreCantor} : x < 1 ↔ x = 0 := by
  obtain (_ | ⟨e, n, a⟩) := x
  · simpa using PreCantor.zero_lt_one
  · rw [← one_def, oadd_lt_oadd]
    simp

end cmp

/-! ### Normal forms -/

/-- A normal form `PreCantor` has the form

`ω ^ e₁ * n₁ + ω ^ e₂ * n₂ + ⋯ + ω ^ eₖ * nₖ`

where `e₁ > e₂ > ⋯ > eₖ` and all the `eᵢ` are also in normal form.

We will essentially only be interested in normal forms, but to avoid complicating the algorithms, we
define everything over `PreCantor` and only prove correctness with normal form as an invariant. -/
inductive NF : PreCantor → Prop
  /-- Zero is a normal form. -/
  | zero : NF 0
  /-- `ω ^ e * n + a` is a normal form when `e` and `a` are normal forms with `a < ω ^ e`. -/
  | oadd' {e n a} : NF e → NF a → a < oadd e 1 0 → NF (oadd e n a)

protected alias NF.oadd := NF.oadd'

theorem NF_oadd_iff {e n a} : NF (oadd e n a) ↔ NF e ∧ NF a ∧ a < oadd e 1 0 := by
  refine ⟨?_, fun ⟨he, ha, h⟩ ↦ he.oadd ha h⟩
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

theorem NF.fst {e n a} (h : NF (oadd e n a)) : NF e := by
  rw [NF_oadd_iff] at h
  exact h.1

theorem NF.snd {e n a} (h : NF (oadd e n a)) : NF a := by
  rw [NF_oadd_iff] at h
  exact h.2.1

theorem NF.lt_oadd {e n a} (h : NF (oadd e n a)) : a < oadd e 1 0 := by
  rw [NF_oadd_iff] at h
  exact h.2.2

theorem NF.oadd_zero {e} (h : NF e) (n : ℕ+) : NF (oadd e n 0) :=
  h.oadd NF.zero (oadd_pos e n 0)

theorem NF.zero_of_zero {e n a} (h : NF (oadd e n a)) (he : e = 0) : a = 0 := by
  subst he
  simpa using h.lt_oadd

theorem NF_natCast (n : ℕ) : NF n := by
  cases n
  · exact NF.zero
  · exact NF.oadd_zero NF.zero _

theorem NF_one : NF 1 :=
  NF_natCast 1

theorem repr_lt_repr_of_lt : ∀ {x y}, NF x → NF y → x < y → repr x < repr y
  | _, 0, _, _, h => by simp at h
  | 0, oadd e n a, _, _, _ => repr_oadd_pos e n a
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, hx, hy, h => by
    rw [oadd_lt_oadd] at h
    have H : repr (oadd e₁ n₁ a₁) < ω ^ e₁.repr * (n₁ + 1 : ℕ+) := by
      simpa [repr_oadd, mul_succ] using repr_lt_repr_of_lt hx.snd (hx.fst.oadd_zero 1) hx.lt_oadd
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
  simpa [repr_oadd] using repr_lt_repr_of_lt hx.snd (hx.fst.oadd_zero 1) hx.lt_oadd

theorem NF.repr_oadd_lt_snd (hx : NF (oadd e n a)) {m} (hn : n < m) :
    repr (oadd e n a) < ω ^ repr e * m := by
  have : (n + 1 : Ordinal) ≤ m := mod_cast Nat.succ_le_of_lt hn
  apply lt_of_lt_of_le _ ((Ordinal.mul_le_mul_iff_left omega0_opow_pos).2 this)
  simpa [repr_oadd, mul_succ] using repr_lt_repr_of_lt hx.snd (hx.fst.oadd_zero 1) hx.lt_oadd

theorem NF.repr_oadd_lt_fst (hx : NF (oadd e n a)) {o} (he : repr e < o) :
    repr (oadd e n a) < ω ^ o :=
  (hx.repr_oadd_lt_snd n.lt_succ_self).trans <| omega0_opow_mul_nat_lt he _

theorem NF.of_dvd_omega0_opow {b e n a} (h : NF (oadd e n a))
    (d : ω ^ b ∣ repr (oadd e n a)) :
    b ≤ repr e ∧ ω ^ b ∣ repr a := by
  sorry
  /-have := mt repr_inj.1 (fun h => by injection h : PreCantor.oadd e n a ≠ 0)
  have L := le_of_not_lt fun l => not_le_of_lt (h.below_of_lt l).repr_lt (le_of_dvd this d)
  simp only [repr] at d
  exact ⟨L, (dvd_add_iff <| (opow_dvd_opow _ L).mul_right _).1 d⟩-/

@[deprecated (since := "2024-09-30")]
alias NF.of_dvd_omega_opow := NF.of_dvd_omega0_opow

theorem NF.of_dvd_omega0 {e n a} (h : NF (PreCantor.oadd e n a)) :
    ω ∣ repr (PreCantor.oadd e n a) → repr e ≠ 0 ∧ ω ∣ repr a := by
  rw [← opow_one ω, ← one_le_iff_ne_zero]
  exact h.of_dvd_omega0_opow

@[deprecated (since := "2024-09-30")]
alias NF.of_dvd_omega := NF.of_dvd_omega0

/-! ### Addition -/

/-- Addition of Cantor normal forms (correct only for normal input) -/
def add : PreCantor → PreCantor → PreCantor
  | 0, o | o, 0 => o
  | oadd e₁ n₁ a₁, x₂@(oadd e₂ n₂ a₂) =>
    match cmp e₁ e₂ with
    | Ordering.lt => x₂
    | Ordering.eq => oadd e₁ (n₁ + n₂) a₂
    | Ordering.gt => oadd e₁ n₁ (add a₁ x₂)

instance : Add PreCantor :=
  ⟨add⟩

@[simp]
theorem add_def (x y : PreCantor) : add x y = x + y :=
  rfl

@[simp]
theorem zero_add (x : PreCantor) : 0 + x = x := by
  cases x <;> rfl

@[simp]
theorem add_zero (x : PreCantor) : x + 0 = x := by
  cases x <;> rfl

theorem oadd_add_oadd_of_lt (h : e₁ < e₂) : oadd e₁ n₁ a₁ + oadd e₂ n₂ a₂ = oadd e₂ n₂ a₂ := by
  rw [← add_def, add, h.cmp_eq_lt]

theorem oadd_add_oadd_of_eq : oadd e n₁ a₁ + oadd e n₂ a₂ = oadd e (n₁ + n₂) a₂ := by
  rw [← add_def, add, _root_.cmp_self_eq_eq]

theorem oadd_add_oadd_of_gt (h : e₂ < e₁) :
    oadd e₁ n₁ a₁ + oadd e₂ n₂ a₂ = oadd e₁ n₁ (a₁ + oadd e₂ n₂ a₂) := by
  rw [← add_def, add, h.cmp_eq_gt, add_def]

theorem repr_add : ∀ {x y}, NF x → NF y → repr (x + y) = repr x + repr y
  | 0, o, _, _ | o, 0, _, _ => by simp
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, hx, hy => by
    obtain h | rfl | h := lt_trichotomy e₁ e₂
    · rw [oadd_add_oadd_of_lt h]
      exact (add_absorp (hx.repr_oadd_lt_fst (repr_lt_repr_of_lt hx.fst hy.fst h))
        (fst_le_repr_oadd _ _ _)).symm
    · rw [oadd_add_oadd_of_eq, repr_oadd, repr_oadd, PNat.add_coe, Nat.cast_add, mul_add,
        add_assoc, add_assoc, add_left_cancel]
      exact (add_absorp hx.repr_lt_oadd (fst_le_repr_oadd _ _ _)).symm
    · rw [oadd_add_oadd_of_gt h, repr_oadd, repr_add hx.snd hy]
      simp [repr_oadd, add_assoc]

theorem NF.add : ∀ {x y}, NF x → NF y → NF (x + y)
  | 0, o, _, _ | o, 0, _, _ => by simpa
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, hx, hy => by
    obtain h | rfl | h := lt_trichotomy e₁ e₂
    · rwa [oadd_add_oadd_of_lt h]
    · rw [oadd_add_oadd_of_eq, NF_oadd_iff]
      exact ⟨hx.fst, hy.snd, hy.lt_oadd⟩
    · rw [oadd_add_oadd_of_gt h, NF_oadd_iff]
      use hx.fst, hx.snd.add hy
      rw [← repr_lt_repr_iff (hx.snd.add hy) (hx.fst.oadd_zero 1), repr_add hx.snd hy]
      simpa [repr_oadd] using principal_add_omega0_opow _ hx.repr_lt_oadd
        (hy.repr_oadd_lt_fst (repr_lt_repr_of_lt hy.fst hx.fst h))

/-! ### Subtraction -/


/-- Subtraction of ordinal notations (correct only for normal input) -/
def sub : PreCantor → PreCantor → PreCantor
  | 0, _ => 0
  | o, 0 => o
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    match cmp e₁ e₂ with
    | Ordering.lt => 0
    | Ordering.gt => o₁
    | Ordering.eq =>
      match (n₁ : ℕ) - n₂ with
      | 0 => if n₁ = n₂ then sub a₁ a₂ else 0
      | Nat.succ k => oadd e₁ k.succPNat a₁

instance : Sub PreCantor :=
  ⟨sub⟩

theorem sub_nfBelow : ∀ {o₁ o₂ b}, NFBelow o₁ b → NF o₂ → NFBelow (o₁ - o₂) b
  | 0, o, b, _, h₂ => by cases o <;> exact NFBelow.zero
  | oadd _ _ _, 0, _, h₁, _ => h₁
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, b, h₁, h₂ => by
    have h' := sub_nfBelow h₁.snd h₂.snd
    simp only [HSub.hSub, Sub.sub, sub] at h' ⊢
    have := @cmp_compares _ _ h₁.fst h₂.fst
    cases h : cmp e₁ e₂
    · apply NFBelow.zero
    · rw [Nat.sub_eq]
      simp only [h, Ordering.compares_eq] at this
      subst e₂
      cases (n₁ : ℕ) - n₂
      · by_cases en : n₁ = n₂ <;> simp only [en, ↓reduceIte]
        · exact h'.mono (le_of_lt h₁.lt)
        · exact NFBelow.zero
      · exact NFBelow.oadd h₁.fst h₁.snd h₁.lt
    · exact h₁

instance sub_nf (o₁ o₂) : ∀ [NF o₁] [NF o₂], NF (o₁ - o₂)
  | ⟨⟨b₁, h₁⟩⟩, h₂ => ⟨⟨b₁, sub_nfBelow h₁ h₂⟩⟩

@[simp]
theorem repr_sub : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ - o₂) = repr o₁ - repr o₂
  | 0, o, _, h₂ => by cases o <;> exact (Ordinal.zero_sub _).symm
  | oadd _ _ _, 0, _, _ => (Ordinal.sub_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
    haveI := h₁.snd; haveI := h₂.snd; have h' := repr_sub a₁ a₂
    conv_lhs at h' => dsimp [HSub.hSub, Sub.sub, sub]
    conv_lhs => dsimp only [HSub.hSub, Sub.sub]; dsimp only [sub]
    have ee := @cmp_compares _ _ h₁.fst h₂.fst
    cases h : cmp e₁ e₂ <;> simp only [h] at ee
    · rw [Ordinal.sub_eq_zero_iff_le.2]
      · rfl
      exact le_of_lt (oadd_lt_oadd_1 h₁ ee)
    · change e₁ = e₂ at ee
      subst e₂
      dsimp only
      cases mn : (n₁ : ℕ) - n₂ <;> dsimp only
      · by_cases en : n₁ = n₂
        · simpa [en]
        · simp only [en, ite_false]
          exact
            (Ordinal.sub_eq_zero_iff_le.2 <|
                le_of_lt <|
                  oadd_lt_oadd_2 h₁ <|
                    lt_of_le_of_ne (tsub_eq_zero_iff_le.1 mn) (mt PNat.eq en)).symm
      · simp [Nat.succPNat]
        rw [(tsub_eq_iff_eq_add_of_le <| le_of_lt <| Nat.lt_of_sub_eq_succ mn).1 mn, add_comm,
          Nat.cast_add, mul_add, add_assoc, add_sub_add_cancel]
        refine
          (Ordinal.sub_eq_of_add_eq <|
              add_absorp h₂.snd'.repr_lt <| le_trans ?_ (le_add_right _ _)).symm
        exact Ordinal.le_mul_left _ (Nat.cast_lt.2 <| Nat.succ_pos _)
    · exact
        (Ordinal.sub_eq_of_add_eq <|
            add_absorp (h₂.below_of_lt ee).repr_lt <| omega0_le_oadd _ _ _).symm

#exit
/-- Multiplication of ordinal notations (correct only for normal input) -/
def mul : PreCantor → PreCantor → PreCantor
  | 0, _ => 0
  | _, 0 => 0
  | o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
    if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (mul o₁ a₂)

instance : Mul PreCantor :=
  ⟨mul⟩

instance : MulZeroClass PreCantor where
  mul := (· * ·)
  zero := 0
  zero_mul o := by cases o <;> rfl
  mul_zero o := by cases o <;> rfl

theorem oadd_mul (e₁ n₁ a₁ e₂ n₂ a₂) :
    oadd e₁ n₁ a₁ * oadd e₂ n₂ a₂ =
      if e₂ = 0 then oadd e₁ (n₁ * n₂) a₁ else oadd (e₁ + e₂) n₂ (oadd e₁ n₁ a₁ * a₂) :=
  rfl

theorem oadd_mul_nfBelow {e₁ n₁ a₁ b₁} (h₁ : NFBelow (oadd e₁ n₁ a₁) b₁) :
    ∀ {o₂ b₂}, NFBelow o₂ b₂ → NFBelow (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂)
  | 0, _, _ => NFBelow.zero
  | oadd e₂ n₂ a₂, b₂, h₂ => by
    have IH := oadd_mul_nfBelow h₁ h₂.snd
    by_cases e0 : e₂ = 0 <;> simp only [e0, oadd_mul, ↓reduceIte]
    · apply NFBelow.oadd h₁.fst h₁.snd
      simpa using (add_lt_add_iff_left (repr e₁)).2 (lt_of_le_of_lt (Ordinal.zero_le _) h₂.lt)
    · haveI := h₁.fst
      haveI := h₂.fst
      apply NFBelow.oadd
      · infer_instance
      · rwa [repr_add]
      · rw [repr_add, add_lt_add_iff_left]
        exact h₂.lt

instance mul_nf : ∀ (o₁ o₂) [NF o₁] [NF o₂], NF (o₁ * o₂)
  | 0, o, _, h₂ => by cases o <;> exact NF.zero
  | oadd _ _ _, _, ⟨⟨_, hb₁⟩⟩, ⟨⟨_, hb₂⟩⟩ => ⟨⟨_, oadd_mul_nfBelow hb₁ hb₂⟩⟩

@[simp]
theorem repr_mul : ∀ (o₁ o₂) [NF o₁] [NF o₂], repr (o₁ * o₂) = repr o₁ * repr o₂
  | 0, o, _, h₂ => by cases o <;> exact (zero_mul _).symm
  | oadd _ _ _, 0, _, _ => (mul_zero _).symm
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ => by
    have IH : repr (mul _ _) = _ := @repr_mul _ _ h₁ h₂.snd
    conv =>
      lhs
      simp [(· * ·)]
    have ao : repr a₁ + ω ^ repr e₁ * (n₁ : ℕ) = ω ^ repr e₁ * (n₁ : ℕ) := by
      apply add_absorp h₁.snd'.repr_lt
      simpa using (Ordinal.mul_le_mul_iff_left <| opow_pos _ omega0_pos).2 (Nat.cast_le.2 n₁.2)
    by_cases e0 : e₂ = 0
    · cases' Nat.exists_eq_succ_of_ne_zero n₂.ne_zero with x xe
      simp only [e0, repr, PNat.mul_coe, natCast_mul, opow_zero, one_mul]
      simp only [xe, h₂.zero_of_zero e0, repr, add_zero]
      rw [natCast_succ x, add_mul_succ _ ao, mul_assoc]
    · simp only [repr]
      haveI := h₁.fst
      haveI := h₂.fst
      simp only [Mul.mul, mul, e0, ite_false, repr.eq_2, repr_add, opow_add, IH, repr, mul_add]
      rw [← mul_assoc]
      congr 2
      have := mt repr_inj.1 e0
      rw [add_mul_limit ao (isLimit_opow_left isLimit_omega0 this), mul_assoc,
        mul_omega0_dvd (Nat.cast_pos'.2 n₁.pos) (nat_lt_omega0 _)]
      simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 this)

/-- Calculate division and remainder of `o` mod `ω`:

`split' o = (a, n)` means `o = ω * a + n`. -/
def split' : PreCantor → PreCantor × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split' a
      (oadd (e - 1) n a', m)

/-- Calculate division and remainder of `o` mod `ω`:

`split o = (a, n)` means `o = a + n`, where `ω ∣ a`. -/
def split : PreCantor → PreCantor × ℕ
  | 0 => (0, 0)
  | oadd e n a =>
    if e = 0 then (0, n)
    else
      let (a', m) := split a
      (oadd e n a', m)

/-- `scale x o` is the ordinal notation for `ω ^ x * o`. -/
def scale (x : PreCantor) : PreCantor → PreCantor
  | 0 => 0
  | oadd e n a => oadd (x + e) n (scale x a)

/-- `mulNat o n` is the ordinal notation for `o * n`. -/
def mulNat : PreCantor → ℕ → PreCantor
  | 0, _ => 0
  | _, 0 => 0
  | oadd e n a, m + 1 => oadd e (n * m.succPNat) a

/-- Auxiliary definition to compute the ordinal notation for the ordinal exponentiation in `opow` -/
def opowAux (e a0 a : PreCantor) : ℕ → ℕ → PreCantor
  | _, 0 => 0
  | 0, m + 1 => oadd e m.succPNat 0
  | k + 1, m => scale (e + mulNat a0 k) a + (opowAux e a0 a k m)

/-- Auxiliary definition to compute the ordinal notation for the ordinal exponentiation in `opow` -/
def opowAux2 (o₂ : PreCantor) (o₁ : PreCantor × ℕ) : PreCantor :=
  match o₁ with
  | (0, 0) => if o₂ = 0 then 1 else 0
  | (0, 1) => 1
  | (0, m + 1) =>
    let (b', k) := split' o₂
    oadd b' (m.succPNat ^ k) 0
  | (a@(oadd a0 _ _), m) =>
    match split o₂ with
    | (b, 0) => oadd (a0 * b) 1 0
    | (b, k + 1) =>
      let eb := a0 * b
      scale (eb + mulNat a0 k) a + opowAux eb a0 (mulNat a m) k m

/-- `opow o₁ o₂` calculates the ordinal notation for the ordinal exponential `o₁ ^ o₂`. -/
def opow (o₁ o₂ : PreCantor) : PreCantor := opowAux2 o₂ (split o₁)

instance : Pow PreCantor PreCantor :=
  ⟨opow⟩

theorem opow_def (o₁ o₂ : PreCantor) : o₁ ^ o₂ = opowAux2 o₂ (split o₁) :=
  rfl

theorem split_eq_scale_split' : ∀ {o o' m} [NF o], split' o = (o', m) → split o = (scale 1 o', m)
  | 0, o', m, _, p => by injection p; substs o' m; rfl
  | oadd e n a, o', m, h, p => by
    by_cases e0 : e = 0 <;> simp only [split', e0, ↓reduceIte, Prod.mk.injEq, split] at p ⊢
    · rcases p with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · revert p
      cases' h' : split' a with a' m'
      haveI := h.fst
      haveI := h.snd
      simp only [split_eq_scale_split' h', and_imp]
      have : 1 + (e - 1) = e := by
        refine repr_inj.1 ?_
        simp only [repr_add, repr, opow_zero, Nat.succPNat_coe, Nat.cast_one, mul_one, add_zero,
          repr_sub]
        have := mt repr_inj.1 e0
        exact Ordinal.add_sub_cancel_of_le <| one_le_iff_ne_zero.2 this
      intros
      substs o' m
      simp [scale, this]

theorem nf_repr_split' : ∀ {o o' m} [NF o], split' o = (o', m) → NF o' ∧ repr o = ω * repr o' + m
  | 0, o', m, _, p => by injection p; substs o' m; simp [NF.zero]
  | oadd e n a, o', m, h, p => by
    by_cases e0 : e = 0 <;> simp [e0, split, split'] at p ⊢
    · rcases p with ⟨rfl, rfl⟩
      simp [h.zero_of_zero e0, NF.zero]
    · revert p
      cases' h' : split' a with a' m'
      haveI := h.fst
      haveI := h.snd
      cases' nf_repr_split' h' with IH₁ IH₂
      simp only [IH₂, and_imp]
      intros
      substs o' m
      have : (ω : Ordinal.{0}) ^ repr e = ω ^ (1 : Ordinal.{0}) * ω ^ (repr e - 1) := by
        have := mt repr_inj.1 e0
        rw [← opow_add, Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)]
      refine ⟨NF.oadd (by infer_instance) _ ?_, ?_⟩
      · simp at this ⊢
        refine
          IH₁.below_of_lt'
            ((Ordinal.mul_lt_mul_iff_left omega0_pos).1 <| lt_of_le_of_lt (le_add_right _ m') ?_)
        rw [← this, ← IH₂]
        exact h.snd'.repr_lt
      · rw [this]
        simp [mul_add, mul_assoc, add_assoc]

theorem scale_eq_mul (x) [NF x] : ∀ (o) [NF o], scale x o = oadd x 1 0 * o
  | 0, _ => rfl
  | oadd e n a, h => by
    simp only [HMul.hMul]; simp only [scale]
    haveI := h.snd
    by_cases e0 : e = 0
    · simp_rw [scale_eq_mul]
      simp [Mul.mul, mul, scale_eq_mul, e0, h.zero_of_zero,
        show x + 0 = x from repr_inj.1 (by simp)]
    · simp [e0, Mul.mul, mul, scale_eq_mul, (· * ·)]

instance nf_scale (x) [NF x] (o) [NF o] : NF (scale x o) := by
  rw [scale_eq_mul]
  infer_instance

@[simp]
theorem repr_scale (x) [NF x] (o) [NF o] : repr (scale x o) = ω ^ repr x * repr o := by
  simp only [scale_eq_mul, repr_mul, repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

theorem nf_repr_split {o o' m} [NF o] (h : split o = (o', m)) : NF o' ∧ repr o = repr o' + m := by
  cases' e : split' o with a n
  cases' nf_repr_split' e with s₁ s₂
  rw [split_eq_scale_split' e] at h
  injection h; substs o' n
  simp only [repr_scale, repr, opow_zero, Nat.succPNat_coe, Nat.cast_one, mul_one, add_zero,
    opow_one, s₂.symm, and_true]
  infer_instance

theorem split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣ repr o' := by
  cases' e : split' o with a n
  rw [split_eq_scale_split' e] at h
  injection h; subst o'
  cases nf_repr_split' e; simp

theorem split_add_lt {o e n a m} [NF o] (h : split o = (oadd e n a, m)) :
    repr a + m < ω ^ repr e := by
  cases' nf_repr_split h with h₁ h₂
  cases' h₁.of_dvd_omega0 (split_dvd h) with e0 d
  apply principal_add_omega0_opow _ h₁.snd'.repr_lt (lt_of_lt_of_le (nat_lt_omega0 _) _)
  simpa using opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 e0)

@[simp]
theorem mulNat_eq_mul (n o) : mulNat o n = o * ofNat n := by cases o <;> cases n <;> rfl

instance nf_mulNat (o) [NF o] (n) : NF (mulNat o n) := by simpa using PreCantor.mul_nf o (ofNat n)

instance nf_opowAux (e a0 a) [NF e] [NF a0] [NF a] : ∀ k m, NF (opowAux e a0 a k m) := by
  intro k m
  unfold opowAux
  cases' m with m m
  · cases k <;> exact NF.zero
  cases' k with k k
  · exact NF.oadd_zero _ _
  · haveI := nf_opowAux e a0 a k
    simp only [Nat.succ_ne_zero m, IsEmpty.forall_iff, mulNat_eq_mul]; infer_instance

instance nf_opow (o₁ o₂) [NF o₁] [NF o₂] : NF (o₁ ^ o₂) := by
  cases' e₁ : split o₁ with a m
  have na := (nf_repr_split e₁).1
  cases' e₂ : split' o₂ with b' k
  haveI := (nf_repr_split' e₂).1
  cases' a with a0 n a'
  · cases' m with m
    · by_cases o₂ = 0 <;> simp only [(· ^ ·), Pow.pow, pow, opow, opowAux2, *] <;> decide
    · by_cases m = 0
      · simp only [(· ^ ·), Pow.pow, pow, opow, opowAux2, *, zero_def]
        decide
      · simp only [(· ^ ·), Pow.pow, pow, opow, opowAux2, mulNat_eq_mul, ofNat, *]
        infer_instance
  · simp only [(· ^ ·), Pow.pow, opow, opowAux2, e₁, split_eq_scale_split' e₂, mulNat_eq_mul]
    have := na.fst
    cases' k with k
    · infer_instance
    · cases k <;> cases m <;> infer_instance

theorem scale_opowAux (e a0 a : PreCantor) [NF e] [NF a0] [NF a] :
    ∀ k m, repr (opowAux e a0 a k m) = ω ^ repr e * repr (opowAux 0 a0 a k m)
  | 0, m => by cases m <;> simp [opowAux]
  | k + 1, m => by
    by_cases h : m = 0
    · simp [h, opowAux, mul_add, opow_add, mul_assoc, scale_opowAux _ _ _ k]
    · -- Porting note: rewrote proof
      rw [opowAux]; swap
      · assumption
      rw [opowAux]; swap
      · assumption
      rw [repr_add, repr_scale, scale_opowAux _ _ _ k]
      simp only [repr_add, repr_scale, opow_add, mul_assoc, zero_add, mul_add]

theorem repr_opow_aux₁ {e a} [Ne : NF e] [Na : NF a] {a' : Ordinal} (e0 : repr e ≠ 0)
    (h : a' < (ω : Ordinal.{0}) ^ repr e) (aa : repr a = a') (n : ℕ+) :
    ((ω : Ordinal.{0}) ^ repr e * (n : ℕ) + a') ^ (ω : Ordinal.{0}) =
      (ω ^ repr e) ^ (ω : Ordinal.{0}) := by
  subst aa
  have No := Ne.oadd n (Na.below_of_lt' h)
  have := omega0_le_oadd e n a
  rw [repr] at this
  refine le_antisymm ?_ (opow_le_opow_left _ this)
  apply (opow_le_of_limit ((opow_pos _ omega0_pos).trans_le this).ne' isLimit_omega0).2
  intro b l
  have := (No.below_of_lt (lt_succ _)).repr_lt
  rw [repr] at this
  apply (opow_le_opow_left b <| this.le).trans
  rw [← opow_mul, ← opow_mul]
  apply opow_le_opow_right omega0_pos
  rcases le_or_lt ω (repr e) with h | h
  · apply (mul_le_mul_left' (le_succ b) _).trans
    rw [← add_one_eq_succ, add_mul_succ _ (one_add_of_omega0_le h), add_one_eq_succ, succ_le_iff,
      Ordinal.mul_lt_mul_iff_left (Ordinal.pos_iff_ne_zero.2 e0)]
    exact isLimit_omega0.2 _ l
  · apply (principal_mul_omega0 (isLimit_omega0.2 _ h) l).le.trans
    simpa using mul_le_mul_right' (one_le_iff_ne_zero.2 e0) ω

section

-- Porting note: `R'` is used in the proof but marked as an unused variable.
set_option linter.unusedVariables false in
theorem repr_opow_aux₂ {a0 a'} [N0 : NF a0] [Na' : NF a'] (m : ℕ) (d : ω ∣ repr a')
    (e0 : repr a0 ≠ 0) (h : repr a' + m < (ω ^ repr a0)) (n : ℕ+) (k : ℕ) :
    let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
    (k ≠ 0 → R < ((ω ^ repr a0) ^ succ (k : Ordinal))) ∧
      ((ω ^ repr a0) ^ (k : Ordinal)) * ((ω ^ repr a0) * (n : ℕ) + repr a') + R =
        ((ω ^ repr a0) * (n : ℕ) + repr a' + m) ^ succ (k : Ordinal) := by
  intro R'
  haveI No : NF (oadd a0 n a') :=
    N0.oadd n (Na'.below_of_lt' <| lt_of_le_of_lt (le_add_right _ _) h)
  induction' k with k IH
  · cases m <;> simp [R', opowAux]
  -- rename R => R'
  let R := repr (opowAux 0 a0 (oadd a0 n a' * ofNat m) k m)
  let ω0 := ω ^ repr a0
  let α' := ω0 * n + repr a'
  change (k ≠ 0 → R < (ω0 ^ succ (k : Ordinal))) ∧ (ω0 ^ (k : Ordinal)) * α' + R
    = (α' + m) ^ (succ ↑k : Ordinal) at IH
  have RR : R' = ω0 ^ (k : Ordinal) * (α' * m) + R := by
    by_cases h : m = 0
    · simp only [R, R', h, PreCantor.ofNat, Nat.cast_zero, zero_add, PreCantor.repr, mul_zero,
        PreCantor.opowAux, add_zero]
    · simp only [R', PreCantor.repr_scale, PreCantor.repr, PreCantor.mulNat_eq_mul, PreCantor.opowAux,
        PreCantor.repr_ofNat, PreCantor.repr_mul, PreCantor.repr_add, Ordinal.opow_mul, PreCantor.zero_add]
  have α0 : 0 < α' := by simpa [lt_def, repr] using oadd_pos a0 n a'
  have ω00 : 0 < ω0 ^ (k : Ordinal) := opow_pos _ (opow_pos _ omega0_pos)
  have Rl : R < ω ^ (repr a0 * succ ↑k) := by
    by_cases k0 : k = 0
    · simp only [k0, Nat.cast_zero, succ_zero, mul_one, R]
      refine lt_of_lt_of_le ?_ (opow_le_opow_right omega0_pos (one_le_iff_ne_zero.2 e0))
      cases' m with m <;> simp [opowAux, omega0_pos]
      rw [← add_one_eq_succ, ← Nat.cast_succ]
      apply nat_lt_omega0
    · rw [opow_mul]
      exact IH.1 k0
  refine ⟨fun _ => ?_, ?_⟩
  · rw [RR, ← opow_mul _ _ (succ k.succ)]
    have e0 := Ordinal.pos_iff_ne_zero.2 e0
    have rr0 : 0 < repr a0 + repr a0 := lt_of_lt_of_le e0 (le_add_left _ _)
    apply principal_add_omega0_opow
    · simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_one_eq_succ,
        opow_mul, opow_succ, mul_assoc]
      rw [Ordinal.mul_lt_mul_iff_left ω00, ← Ordinal.opow_add]
      have : _ < ω ^ (repr a0 + repr a0) := (No.below_of_lt ?_).repr_lt
      · exact mul_lt_omega0_opow rr0 this (nat_lt_omega0 _)
      · simpa using (add_lt_add_iff_left (repr a0)).2 e0
    · exact
        lt_of_lt_of_le Rl
          (opow_le_opow_right omega0_pos <|
            mul_le_mul_left' (succ_le_succ_iff.2 (Nat.cast_le.2 (le_of_lt k.lt_succ_self))) _)
  calc
    (ω0 ^ (k.succ : Ordinal)) * α' + R'
    _ = (ω0 ^ succ (k : Ordinal)) * α' + ((ω0 ^ (k : Ordinal)) * α' * m + R) := by
        rw [natCast_succ, RR, ← mul_assoc]
    _ = ((ω0 ^ (k : Ordinal)) * α' + R) * α' + ((ω0 ^ (k : Ordinal)) * α' + R) * m := ?_
    _ = (α' + m) ^ succ (k.succ : Ordinal) := by rw [← mul_add, natCast_succ, opow_succ, IH.2]
  congr 1
  · have αd : ω ∣ α' :=
      dvd_add (dvd_mul_of_dvd_left (by simpa using opow_dvd_opow ω (one_le_iff_ne_zero.2 e0)) _) d
    rw [mul_add (ω0 ^ (k : Ordinal)), add_assoc, ← mul_assoc, ← opow_succ,
      add_mul_limit _ (isLimit_iff_omega0_dvd.2 ⟨ne_of_gt α0, αd⟩), mul_assoc,
      @mul_omega0_dvd n (Nat.cast_pos'.2 n.pos) (nat_lt_omega0 _) _ αd]
    apply @add_absorp _ (repr a0 * succ ↑k)
    · refine principal_add_omega0_opow _ ?_ Rl
      rw [opow_mul, opow_succ, Ordinal.mul_lt_mul_iff_left ω00]
      exact No.snd'.repr_lt
    · have := mul_le_mul_left' (one_le_iff_pos.2 <| Nat.cast_pos'.2 n.pos) (ω0 ^ succ (k : Ordinal))
      rw [opow_mul]
      simpa [-opow_succ]
  · cases m
    · have : R = 0 := by cases k <;> simp [R, opowAux]
      simp [this]
    · rw [natCast_succ, add_mul_succ]
      apply add_absorp Rl
      rw [opow_mul, opow_succ]
      apply mul_le_mul_left'
      simpa [repr] using omega0_le_oadd a0 n a'

end

theorem repr_opow (o₁ o₂) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = repr o₁ ^ repr o₂ := by
  cases' e₁ : split o₁ with a m
  cases' nf_repr_split e₁ with N₁ r₁
  cases' a with a0 n a'
  · cases' m with m
    · by_cases h : o₂ = 0 <;> simp [opow_def, opowAux2, opow, e₁, h, r₁]
      have := mt repr_inj.1 h
      rw [zero_opow this]
    · cases' e₂ : split' o₂ with b' k
      cases' nf_repr_split' e₂ with _ r₂
      by_cases h : m = 0
      · simp [opow_def, opow, e₁, h, r₁, e₂, r₂]
      simp only [opow_def, opowAux2, opow, e₁, h, r₁, e₂, r₂, repr,
          opow_zero, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_zero, _root_.zero_add, mul_one,
          add_zero, one_opow, npow_eq_pow]
      rw [opow_add, opow_mul, opow_omega0, add_one_eq_succ]
      · congr
        conv_lhs =>
          dsimp [(· ^ ·)]
          simp [Pow.pow, opow, Ordinal.succ_ne_zero]
        rw [opow_natCast]
      · simpa [Nat.one_le_iff_ne_zero]
      · rw [← Nat.cast_succ, lt_omega0]
        exact ⟨_, rfl⟩
  · haveI := N₁.fst
    haveI := N₁.snd
    cases' N₁.of_dvd_omega0 (split_dvd e₁) with a00 ad
    have al := split_add_lt e₁
    have aa : repr (a' + ofNat m) = repr a' + m := by
      simp only [eq_self_iff_true, PreCantor.repr_ofNat, PreCantor.repr_add]
    cases' e₂ : split' o₂ with b' k
    cases' nf_repr_split' e₂ with _ r₂
    simp only [opow_def, opow, e₁, r₁, split_eq_scale_split' e₂, opowAux2, repr]
    cases' k with k
    · simp [r₂, opow_mul, repr_opow_aux₁ a00 al aa, add_assoc]
    · simp? [r₂, opow_add, opow_mul, mul_assoc, add_assoc, -repr, -opow_natCast] says
        simp only [mulNat_eq_mul, repr_add, repr_scale, repr_mul, repr_ofNat, opow_add, opow_mul,
          mul_assoc, add_assoc, r₂, Nat.cast_add, Nat.cast_one, add_one_eq_succ, opow_succ]
      simp only [repr, opow_zero, Nat.succPNat_coe, Nat.cast_one, mul_one, add_zero, opow_one]
      rw [repr_opow_aux₁ a00 al aa, scale_opowAux]
      simp only [repr_mul, repr_scale, repr, opow_zero, Nat.succPNat_coe, Nat.cast_one, mul_one,
        add_zero, opow_one, opow_mul]
      rw [← mul_add, ← add_assoc ((ω : Ordinal.{0}) ^ repr a0 * (n : ℕ))]
      congr 1
      rw [← opow_succ]
      exact (repr_opow_aux₂ _ ad a00 al _ _).2

/-- Given an ordinal, returns:

* `inl none` for `0`
* `inl (some a)` for `a + 1`
* `inr f` for a limit ordinal `a`, where `f i` is a sequence converging to `a` -/
def fundamentalSequence : PreCantor → (Option PreCantor) ⊕ (ℕ → PreCantor)
  | zero => Sum.inl none
  | oadd a m b =>
    match fundamentalSequence b with
    | Sum.inr f => Sum.inr fun i => oadd a m (f i)
    | Sum.inl (some b') => Sum.inl (some (oadd a m b'))
    | Sum.inl none =>
      match fundamentalSequence a, m.natPred with
      | Sum.inl none, 0 => Sum.inl (some zero)
      | Sum.inl none, m + 1 => Sum.inl (some (oadd zero m.succPNat zero))
      | Sum.inl (some a'), 0 => Sum.inr fun i => oadd a' i.succPNat zero
      | Sum.inl (some a'), m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd a' i.succPNat zero)
      | Sum.inr f, 0 => Sum.inr fun i => oadd (f i) 1 zero
      | Sum.inr f, m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd (f i) 1 zero)

private theorem exists_lt_add {α} [hα : Nonempty α] {o : Ordinal} {f : α → Ordinal}
    (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) {b : Ordinal} ⦃a⦄ (h : a < b + o) : ∃ i, a < b + f i := by
  cases' lt_or_le a b with h h'
  · obtain ⟨i⟩ := id hα
    exact ⟨i, h.trans_le (le_add_right _ _)⟩
  · rw [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left] at h
    refine (H h).imp fun i H => ?_
    rwa [← Ordinal.add_sub_cancel_of_le h', add_lt_add_iff_left]

private theorem exists_lt_mul_omega0' {o : Ordinal} ⦃a⦄ (h : a < o * ω) :
    ∃ i : ℕ, a < o * ↑i + o := by
  obtain ⟨i, hi, h'⟩ := (lt_mul_of_limit isLimit_omega0).1 h
  obtain ⟨i, rfl⟩ := lt_omega0.1 hi
  exact ⟨i, h'.trans_le (le_add_right _ _)⟩

private theorem exists_lt_omega0_opow' {α} {o b : Ordinal} (hb : 1 < b) (ho : o.IsLimit)
    {f : α → Ordinal} (H : ∀ ⦃a⦄, a < o → ∃ i, a < f i) ⦃a⦄ (h : a < b ^ o) :
        ∃ i, a < b ^ f i := by
  obtain ⟨d, hd, h'⟩ := (lt_opow_of_limit (zero_lt_one.trans hb).ne' ho).1 h
  exact (H hd).imp fun i hi => h'.trans <| (opow_lt_opow_iff_right hb).2 hi

/-- The property satisfied by `fundamentalSequence o`:

* `inl none` means `o = 0`
* `inl (some a)` means `o = succ a`
* `inr f` means `o` is a limit ordinal and `f` is a strictly increasing sequence which converges to
  `o` -/
def FundamentalSequenceProp (o : PreCantor) : (Option PreCantor) ⊕ (ℕ → PreCantor) → Prop
  | Sum.inl none => o = 0
  | Sum.inl (some a) => o.repr = succ a.repr ∧ (o.NF → a.NF)
  | Sum.inr f =>
    o.repr.IsLimit ∧
      (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧ ∀ a, a < o.repr → ∃ i, a < (f i).repr

theorem fundamentalSequenceProp_inl_none (o) :
    FundamentalSequenceProp o (Sum.inl none) ↔ o = 0 :=
  Iff.rfl

theorem fundamentalSequenceProp_inl_some (o a) :
    FundamentalSequenceProp o (Sum.inl (some a)) ↔ o.repr = succ a.repr ∧ (o.NF → a.NF) :=
  Iff.rfl

theorem fundamentalSequenceProp_inr (o f) :
    FundamentalSequenceProp o (Sum.inr f) ↔
      o.repr.IsLimit ∧
        (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧
        ∀ a, a < o.repr → ∃ i, a < (f i).repr :=
  Iff.rfl

theorem fundamentalSequence_has_prop (o) : FundamentalSequenceProp o (fundamentalSequence o) := by
  induction' o with a m b iha ihb; · exact rfl
  rw [fundamentalSequence]
  rcases e : b.fundamentalSequence with (⟨_ | b'⟩ | f) <;>
    simp only [FundamentalSequenceProp] <;>
    rw [e, FundamentalSequenceProp] at ihb
  · rcases e : a.fundamentalSequence with (⟨_ | a'⟩ | f) <;> cases' e' : m.natPred with m' <;>
      simp only [FundamentalSequenceProp] <;>
      rw [e, FundamentalSequenceProp] at iha <;>
      (try rw [show m = 1 by
            have := PNat.natPred_add_one m; rw [e'] at this; exact PNat.coe_inj.1 this.symm]) <;>
      (try rw [show m = (m' + 1).succPNat by
              rw [← e', ← PNat.coe_inj, Nat.succPNat_coe, ← Nat.add_one, PNat.natPred_add_one]]) <;>
      simp only [repr, iha, ihb, opow_lt_opow_iff_right one_lt_omega0, add_lt_add_iff_left,
        add_zero, eq_self_iff_true, lt_add_iff_pos_right, lt_def, mul_one, Nat.cast_zero,
        Nat.cast_succ, Nat.succPNat_coe, opow_succ, opow_zero, mul_add_one, PNat.one_coe, succ_zero,
        _root_.zero_add, zero_def]
    · decide
    · exact ⟨rfl, inferInstance⟩
    · have := opow_pos (repr a') omega0_pos
      refine
        ⟨isLimit_mul this isLimit_omega0, fun i =>
          ⟨this, ?_, fun H => @NF.oadd_zero _ _ (iha.2 H.fst)⟩, exists_lt_mul_omega0'⟩
      rw [← mul_succ, ← natCast_succ, Ordinal.mul_lt_mul_iff_left this]
      apply nat_lt_omega0
    · have := opow_pos (repr a') omega0_pos
      refine
        ⟨isLimit_add _ (isLimit_mul this isLimit_omega0), fun i => ⟨this, ?_, ?_⟩,
          exists_lt_add exists_lt_mul_omega0'⟩
      · rw [← mul_succ, ← natCast_succ, Ordinal.mul_lt_mul_iff_left this]
        apply nat_lt_omega0
      · refine fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (@NF.oadd_zero _ _ (iha.2 H.fst)))
        rw [repr, ← zero_def, repr, add_zero, iha.1, opow_succ, Ordinal.mul_lt_mul_iff_left this]
        apply nat_lt_omega0
    · rcases iha with ⟨h1, h2, h3⟩
      refine ⟨isLimit_opow one_lt_omega0 h1, fun i => ?_,
        exists_lt_omega0_opow' one_lt_omega0 h1 h3⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      exact ⟨h4, h5, fun H => @NF.oadd_zero _ _ (h6 H.fst)⟩
    · rcases iha with ⟨h1, h2, h3⟩
      refine
        ⟨isLimit_add _ (isLimit_opow one_lt_omega0 h1), fun i => ?_,
          exists_lt_add (exists_lt_omega0_opow' one_lt_omega0 h1 h3)⟩
      obtain ⟨h4, h5, h6⟩ := h2 i
      refine ⟨h4, h5, fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (@NF.oadd_zero _ _ (h6 H.fst)))⟩
      rwa [repr, ← zero_def, repr, add_zero, PNat.one_coe, Nat.cast_one, mul_one,
        opow_lt_opow_iff_right one_lt_omega0]
  · refine ⟨by
      rw [repr, ihb.1, add_succ, repr], fun H => H.fst.oadd _ (NF.below_of_lt' ?_ (ihb.2 H.snd))⟩
    have := H.snd'.repr_lt
    rw [ihb.1] at this
    exact (lt_succ _).trans this
  · rcases ihb with ⟨h1, h2, h3⟩
    simp only [repr]
    exact
      ⟨Ordinal.isLimit_add _ h1, fun i =>
        ⟨oadd_lt_oadd_3 (h2 i).1, oadd_lt_oadd_3 (h2 i).2.1, fun H =>
          H.fst.oadd _ (NF.below_of_lt' (lt_trans (h2 i).2.1 H.snd'.repr_lt) ((h2 i).2.2 H.snd))⟩,
        exists_lt_add h3⟩

/-- The fast growing hierarchy for ordinal notations `< ε₀`. This is a sequence of functions `ℕ → ℕ`
indexed by ordinals, with the definition:

* `f_0(n) = n + 1`
* `f_(α + 1)(n) = f_α^[n](n)`
* `f_α(n) = f_(α[n])(n)` where `α` is a limit ordinal and `α[i]` is the fundamental sequence
  converging to `α` -/
def fastGrowing : PreCantor → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => Nat.succ
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; apply lt_succ
      fun i => (fastGrowing a)^[i] i
    | Sum.inr f, h => fun i =>
      have : f i < o := (h.2.1 i).2.1
      fastGrowing (f i) i
  termination_by o => o

-- Porting note: the linter bug should be fixed.
@[nolint unusedHavesSuffices]
theorem fastGrowing_def {o : PreCantor} {x} (e : fundamentalSequence o = x) :
    fastGrowing o =
      match
        (motive := (x : Option PreCantor ⊕ (ℕ → PreCantor)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => Nat.succ
      | Sum.inl (some a), _ =>
        fun i => (fastGrowing a)^[i] i
      | Sum.inr f, _ => fun i =>
        fastGrowing (f i) i := by
  subst x
  rw [fastGrowing]

theorem fastGrowing_zero' (o : PreCantor) (h : fundamentalSequence o = Sum.inl none) :
    fastGrowing o = Nat.succ := by
  rw [fastGrowing_def h]

theorem fastGrowing_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    fastGrowing o = fun i => (fastGrowing a)^[i] i := by
  rw [fastGrowing_def h]

theorem fastGrowing_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    fastGrowing o = fun i => fastGrowing (f i) i := by
  rw [fastGrowing_def h]

@[simp]
theorem fastGrowing_zero : fastGrowing 0 = Nat.succ :=
  fastGrowing_zero' _ rfl

@[simp]
theorem fastGrowing_one : fastGrowing 1 = fun n => 2 * n := by
  rw [@fastGrowing_succ 1 0 rfl]; funext i; rw [two_mul, fastGrowing_zero]
  suffices ∀ a b, Nat.succ^[a] b = b + a from this _ _
  intro a b; induction a <;> simp [*, Function.iterate_succ', Nat.add_assoc, -Function.iterate_succ]

@[simp]
theorem fastGrowing_two : fastGrowing 2 = fun n => (2 ^ n) * n := by
  rw [@fastGrowing_succ 2 1 rfl]; funext i; rw [fastGrowing_one]
  suffices ∀ a b, (fun n : ℕ => 2 * n)^[a] b = (2 ^ a) * b from this _ _
  intro a b; induction a <;>
    simp [*, Function.iterate_succ, pow_succ, mul_assoc, -Function.iterate_succ]

/-- We can extend the fast growing hierarchy one more step to `ε₀` itself, using `ω ^ (ω ^ (⋯ ^ ω))`
as the fundamental sequence converging to `ε₀` (which is not an `PreCantor`). Extending the fast
growing hierarchy beyond this requires a definition of fundamental sequence for larger ordinals. -/
def fastGrowingε₀ (i : ℕ) : ℕ :=
  fastGrowing ((fun a => a.oadd 1 0)^[i] 0) i

theorem fastGrowingε₀_zero : fastGrowingε₀ 0 = 1 := by simp [fastGrowingε₀]

theorem fastGrowingε₀_one : fastGrowingε₀ 1 = 2 := by
  simp [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl]

theorem fastGrowingε₀_two : fastGrowingε₀ 2 = 2048 := by
  norm_num [fastGrowingε₀, show oadd 0 1 0 = 1 from rfl, @fastGrowing_limit (oadd 1 1 0) _ rfl,
    show oadd 0 (2 : Nat).succPNat 0 = 3 from rfl, @fastGrowing_succ 3 2 rfl]

end PreCantor

/-- The type of normal ordinal notations.

It would have been nicer to define this right in the inductive type, but `NF o` requires `repr`
which requires `PreCantor`, so all these things would have to be defined at once, which messes up the VM
representation. -/
def Cantor :=
  { o : PreCantor // o.NF }

instance : DecidableEq Cantor := by unfold Cantor; infer_instance

namespace Cantor

open PreCantor

instance NF (o : Cantor) : NF o.1 :=
  o.2

/-- Construct a `Cantor` from an ordinal notation (and infer normality) -/
def mk (o : PreCantor) [h : PreCantor.NF o] : Cantor :=
  ⟨o, h⟩

/-- The ordinal represented by an ordinal notation.

This function is noncomputable because ordinal arithmetic is noncomputable. In computational
applications `Cantor` can be used exclusively without reference to `Ordinal`, but this function
allows for correctness results to be stated. -/
noncomputable def repr (o : Cantor) : Ordinal :=
  o.1.repr

instance : ToString Cantor :=
  ⟨fun x => x.1.toString⟩

instance : Repr Cantor :=
  ⟨fun x prec => x.1.repr' prec⟩

instance : Preorder Cantor where
  le x y := repr x ≤ repr y
  lt x y := repr x < repr y
  le_refl _ := @le_refl Ordinal _ _
  le_trans _ _ _ := @le_trans Ordinal _ _ _ _
  lt_iff_le_not_le _ _ := @lt_iff_le_not_le Ordinal _ _ _

instance : Zero Cantor :=
  ⟨⟨0, NF.zero⟩⟩

instance : Inhabited Cantor :=
  ⟨0⟩

theorem lt_wf : @WellFounded Cantor (· < ·) :=
  InvImage.wf repr Ordinal.lt_wf

instance : WellFoundedLT Cantor :=
  ⟨lt_wf⟩

instance : WellFoundedRelation Cantor :=
  ⟨(· < ·), lt_wf⟩

/-- Convert a natural number to an ordinal notation -/
def ofNat (n : ℕ) : Cantor :=
  ⟨PreCantor.ofNat n, ⟨⟨_, nfBelow_ofNat _⟩⟩⟩

/-- Compare ordinal notations -/
def cmp (a b : Cantor) : Ordering :=
  PreCantor.cmp a.1 b.1

theorem cmp_compares : ∀ a b : Cantor, (cmp a b).Compares a b
  | ⟨a, ha⟩, ⟨b, hb⟩ => by
    dsimp [cmp]
    have := PreCantor.cmp_compares a b
    cases h : PreCantor.cmp a b <;> simp only [h] at this <;> try exact this
    exact Subtype.mk_eq_mk.2 this

instance : LinearOrder Cantor :=
  linearOrderOfCompares cmp cmp_compares

instance : IsWellOrder Cantor (· < ·) where

/-- Asserts that `repr a < ω ^ repr b`. Used in `Cantor.recOn`. -/
def below (a b : Cantor) : Prop :=
  NFBelow a.1 (repr b)

/-- The `oadd` pseudo-constructor for `Cantor` -/
def oadd (e : Cantor) (n : ℕ+) (a : Cantor) (h : below a e) : Cantor :=
  ⟨_, NF.oadd e.2 n h⟩

/-- This is a recursor-like theorem for `Cantor` suggesting an inductive definition, which can't
actually be defined this way due to conflicting dependencies. -/
@[elab_as_elim]
def recOn {C : Cantor → Sort*} (o : Cantor) (H0 : C 0)
    (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) : C o := by
  cases' o with o h; induction' o with e n a IHe IHa
  · exact H0
  · exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _)

/-- Addition of ordinal notations -/
instance : Add Cantor :=
  ⟨fun x y => mk (x.1 + y.1)⟩

theorem repr_add (a b) : repr (a + b) = repr a + repr b :=
  PreCantor.repr_add a.1 b.1

/-- Subtraction of ordinal notations -/
instance : Sub Cantor :=
  ⟨fun x y => mk (x.1 - y.1)⟩

theorem repr_sub (a b) : repr (a - b) = repr a - repr b :=
  PreCantor.repr_sub a.1 b.1

/-- Multiplication of ordinal notations -/
instance : Mul Cantor :=
  ⟨fun x y => mk (x.1 * y.1)⟩

theorem repr_mul (a b) : repr (a * b) = repr a * repr b :=
  PreCantor.repr_mul a.1 b.1

/-- Exponentiation of ordinal notations -/
def opow (x y : Cantor) :=
  mk (x.1 ^ y.1)

theorem repr_opow (a b) : repr (opow a b) = repr a ^ repr b :=
  PreCantor.repr_opow a.1 b.1

end Cantor
