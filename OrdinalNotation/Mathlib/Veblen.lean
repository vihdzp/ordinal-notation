/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import OrdinalNotation.Mathlib.Card

/-!
# Veblen hierarchy

We define the two-argument Veblen function, which satisfes `veblen 0 a = ω ^ a` and that for
`a ≠ 0`, `veblen a` enumerates the common fixed points of `veblen b` for `b < a`.

We use this to define two important functions on ordinals: the epsilon function `ε_ o = veblen 1 o`,
and the gamma function `Γ_ o` enumerating the fixed points of `veblen · 0`.

## Main definitions

* `veblenWith`: The Veblen hierarchy with a specified initial function.
* `veblen`: The Veblen hierarchy starting with `ω ^ ·`.

## Notation

The following notation is scoped to the `Ordinal` namespace.

- `ε_ o` is notation for `veblen 1 o`. `ε₀` is notation for `ε_ 0`.
- `Γ_ o` is notation for `gamma o`. `Γ₀` is notation for `Γ_ 0`.

## Todo

- Prove that the exponential principal ordinals are the epsilon ordinals (and 0, 1, 2, ω).
- Prove that the ordinals principal under `veblen` are the gamma ordinals (and 0).
-/

noncomputable section

universe u

namespace Cardinal

theorem max_zero_left (a : Cardinal) : max 0 a = a :=
  max_bot_left a

theorem max_zero_right (a : Cardinal) : max a 0 = a :=
  max_bot_right a

theorem mul_le_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) : a * b ≤ a := by
  obtain rfl | hb' := eq_or_ne b 0
  · simp
  · rw [mul_eq_left ha hb hb']

theorem mul_le_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) : a * b ≤ b := by
  rw [mul_comm]
  exact mul_le_left hb ha

theorem mul_le {a b c : Cardinal} (ha : a ≤ c) (hb : b ≤ c) (hc : ℵ₀ ≤ c) : a * b ≤ c :=
  (mul_le_max _ _).trans <| max_le (max_le ha hb) hc

end Cardinal

open Cardinal

namespace Ordinal

variable {f : Ordinal.{u} → Ordinal.{u}} {o a b c d : Ordinal.{u}}

-- TODO: move to `FixedPoint` file
theorem derivFamily_strictMono {ι} {f : ι → Ordinal.{u} → Ordinal.{u}} [Small.{u} ι]
    (H : ∀ i, IsNormal (f i)) : StrictMono (derivFamily f) := by
  rw [derivFamily_eq_enumOrd H]
  exact enumOrd_strictMono (not_bddAbove_fp_family H)

-- TODO: move to `FixedPoint` file
theorem deriv_strictMono {f} (H : IsNormal f) : StrictMono (deriv f) :=
  derivFamily_strictMono fun _ ↦ H

/-! ### Veblen function with a given starting function -/

/-- `veblenWith f o` is the `o`-th function in the Veblen hierarchy starting with `f`. This is
defined so that

- `veblenWith f 0 = f`.
- `veblenWith f a` enumerates the fixed points of `veblenWith f b` for `b < a` when `a ≠ 0`.
-/
@[pp_nodot]
def veblenWith (f : Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  if o = 0 then f else derivFamily fun x : Set.Iio o ↦ veblenWith f x.1
termination_by o
decreasing_by exact x.2

@[simp]
theorem veblenWith_zero (f : Ordinal → Ordinal) : veblenWith f 0 = f := by
  rw [veblenWith, if_pos rfl]

theorem veblenWith_of_ne_zero (f : Ordinal → Ordinal) (h : o ≠ 0) :
    veblenWith f o = derivFamily fun x : Set.Iio o ↦ veblenWith f x.1 := by
  rw [veblenWith, if_neg h]

/-- `veblenWith f o` is always normal for `o ≠ 0`. -/
theorem isNormal_veblenWith' (f : Ordinal → Ordinal) (h : o ≠ 0) : IsNormal (veblenWith f o) := by
  rw [veblenWith_of_ne_zero f h]
  exact isNormal_derivFamily _

/-- `veblenWith f o` is always normal whenever `f` is. -/
theorem isNormal_veblenWith (hf : IsNormal f) (o : Ordinal) : IsNormal (veblenWith f o) := by
  obtain rfl | h := eq_or_ne o 0
  · rwa [veblenWith_zero]
  · exact isNormal_veblenWith' f h

theorem veblenWith_veblenWith_of_lt (hf : IsNormal f) (h : a < b) (c : Ordinal) :
    veblenWith f a (veblenWith f b c) = veblenWith f b c := by
  let x : {a // a < b} := ⟨a, h⟩
  rw [veblenWith_of_ne_zero f h.bot_lt.ne',
    derivFamily_fp (f := fun x : Set.Iio b ↦ veblenWith f x.1) (i := x)]
  exact isNormal_veblenWith hf x

theorem veblenWith_succ (hf : IsNormal f) (o : Ordinal) :
    veblenWith f (Order.succ o) = deriv (veblenWith f o) := by
  rw [deriv_eq_enumOrd (isNormal_veblenWith hf o), veblenWith_of_ne_zero f (succ_ne_zero _),
    derivFamily_eq_enumOrd]
  · apply congr_arg
    ext a
    rw [Set.mem_iInter]
    use fun ha ↦ ha ⟨o, Order.lt_succ o⟩
    rintro (ha : _ = _) ⟨b, hb : b < _⟩
    obtain rfl | hb := Order.lt_succ_iff_eq_or_lt.1 hb
    · rw [Function.mem_fixedPoints_iff, ha]
    · rw [← ha]
      exact veblenWith_veblenWith_of_lt hf hb _
  · exact fun a ↦ isNormal_veblenWith hf a

theorem veblenWith_right_strictMono (hf : IsNormal f) (o : Ordinal) :
    StrictMono (veblenWith f o) := by
  obtain rfl | h := eq_or_ne o 0
  · rw [veblenWith_zero]
    exact hf.strictMono
  · rw [veblenWith_of_ne_zero f h]
    exact derivFamily_strictMono fun a ↦ isNormal_veblenWith hf a

theorem veblenWith_right_monotone (hf : IsNormal f) (o : Ordinal) :
    Monotone (veblenWith f o) :=
  (veblenWith_right_strictMono hf o).monotone

theorem veblenWith_lt_veblenWith_right_iff (hf : IsNormal f) :
    veblenWith f o a < veblenWith f o b ↔ a < b :=
  (veblenWith_right_strictMono hf o).lt_iff_lt

theorem veblenWith_le_veblenWith_right_iff (hf : IsNormal f) :
    veblenWith f o a ≤ veblenWith f o b ↔ a ≤ b :=
  (veblenWith_right_strictMono hf o).le_iff_le

theorem veblenWith_inj (hf : IsNormal f) :
    veblenWith f o a = veblenWith f o b ↔ a = b :=
  (veblenWith_right_strictMono hf o).injective.eq_iff

theorem right_le_veblenWith (hf : IsNormal f) (a b : Ordinal) :
    b ≤ veblenWith f a b :=
  (veblenWith_right_strictMono hf a).le_apply

theorem veblenWith_left_monotone (hf : IsNormal f) (o : Ordinal) :
    Monotone fun a ↦ veblenWith f a o := by
  rw [monotone_iff_forall_lt]
  intro a b h
  rw [← veblenWith_veblenWith_of_lt hf h]
  exact (veblenWith_right_strictMono hf a).monotone (right_le_veblenWith hf b o)

theorem veblenWith_pos (hf : IsNormal f) (hp : 0 < f 0) (a b : Ordinal) : 0 < veblenWith f a b := by
  have H (b) : 0 < veblenWith f 0 b := by
    rw [veblenWith_zero]
    exact hp.trans_le (hf.monotone (Ordinal.zero_le _))
  obtain rfl | h := Ordinal.eq_zero_or_pos a
  · exact H b
  · rw [← veblenWith_veblenWith_of_lt hf h]
    exact H _

theorem veblenWith_zero_strictMono (hf : IsNormal f) (hp : 0 < f 0) :
    StrictMono (veblenWith f · 0) := by
  intro a b h
  dsimp only
  rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_lt_veblenWith_right_iff hf]
  exact veblenWith_pos hf hp b 0

theorem veblenWith_zero_monotone (hf : IsNormal f) (hp : 0 < f 0) :
    Monotone (veblenWith f · 0) :=
  (veblenWith_zero_strictMono hf hp).monotone

theorem veblenWith_zero_lt_iff (hf : IsNormal f) (hp : 0 < f 0) :
    veblenWith f a 0 < veblenWith f b 0 ↔ a < b :=
  (veblenWith_zero_strictMono hf hp).lt_iff_lt

theorem veblenWith_zero_le_iff (hf : IsNormal f) (hp : 0 < f 0) :
    veblenWith f a 0 ≤ veblenWith f b 0 ↔ a ≤ b :=
  (veblenWith_zero_strictMono hf hp).le_iff_le

theorem veblenWith_zero_inj (hf : IsNormal f) (hp : 0 < f 0) :
    veblenWith f a 0 = veblenWith f b 0 ↔ a = b :=
  (veblenWith_zero_strictMono hf hp).injective.eq_iff

theorem left_le_veblenWith (hf : IsNormal f) (hp : 0 < f 0) (a b : Ordinal) :
    a ≤ veblenWith f a b :=
  (veblenWith_zero_strictMono hf hp).le_apply.trans <|
    veblenWith_right_monotone hf _ (Ordinal.zero_le _)

theorem isNormal_veblenWith_zero (hf : IsNormal f) (hp : 0 < f 0) :
    IsNormal (veblenWith f · 0) := by
  rw [isNormal_iff_strictMono_limit]
  refine ⟨veblenWith_zero_strictMono hf hp, fun o ho a IH ↦ ?_⟩
  rw [veblenWith_of_ne_zero f ho.pos.ne', derivFamily_zero]
  apply nfpFamily_le fun l ↦ ?_
  suffices ∃ b < o, List.foldr _ 0 l ≤ veblenWith f b 0 by
    obtain ⟨b, hb, hb'⟩ := this
    exact hb'.trans (IH b hb)
  induction l with
  | nil => use 0; simp [ho.pos]
  | cons a l IH =>
    obtain ⟨b, hb, hb'⟩ := IH
    refine ⟨_, ho.succ_lt (max_lt a.2 hb), (veblenWith_right_monotone hf _ <| hb'.trans <|
      veblenWith_left_monotone hf _ <| (le_max_right a.1 b).trans (Order.le_succ _)).trans ?_⟩
    rw [veblenWith_veblenWith_of_lt hf]
    rw [Order.lt_succ_iff]
    exact le_max_left _ b

theorem veblenWith_lt_veblenWith_iff (hf : IsNormal f) {a b c d : Ordinal} :
    veblenWith f a b < veblenWith f c d ↔
    a = c ∧ b < d ∨ a < c ∧ b < veblenWith f c d ∨ c < a ∧ veblenWith f a b < d := by
  obtain h | rfl | h := lt_trichotomy a c
  · simp_rw [h, h.ne, h.not_lt, false_and, false_or, or_false, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_lt_veblenWith_right_iff hf]
  · simp [veblenWith_lt_veblenWith_right_iff hf]
  · simp_rw [h, h.ne', h.not_lt, false_and, false_or, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_lt_veblenWith_right_iff hf]

theorem veblenWith_le_veblenWith_iff (hf : IsNormal f) {a b c d : Ordinal} :
    veblenWith f a b ≤ veblenWith f c d ↔
    a = c ∧ b ≤ d ∨ a < c ∧ b ≤ veblenWith f c d ∨ c < a ∧ veblenWith f a b ≤ d := by
  obtain h | rfl | h := lt_trichotomy a c
  · simp_rw [h, h.ne, h.not_lt, false_and, false_or, or_false, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_le_veblenWith_right_iff hf]
  · simp [veblenWith_le_veblenWith_right_iff hf]
  · simp_rw [h, h.ne', h.not_lt, false_and, false_or, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_le_veblenWith_right_iff hf]

theorem veblenWith_eq_veblenWith_iff (hf : IsNormal f) {a b c d : Ordinal} :
    veblenWith f a b = veblenWith f c d ↔
    a = c ∧ b = d ∨ a < c ∧ b = veblenWith f c d ∨ c < a ∧ veblenWith f a b = d := by
  obtain h | rfl | h := lt_trichotomy a c
  · simp_rw [h, h.ne, h.not_lt, false_and, false_or, or_false, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_inj hf]
  · simp [veblenWith_inj hf]
  · simp_rw [h, h.ne', h.not_lt, false_and, false_or, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_inj hf]

/-! ### Veblen function -/

private theorem isNormal_omega0_opow : IsNormal fun a ↦ ω ^ a := isNormal_opow one_lt_omega0
private theorem omega0_opow_zero_pos : 0 < ω ^ (0 : Ordinal) := by simp

/-- `veblen o` is the `o`-th function in the Veblen hierarchy starting with `ω ^ ·`. That is:

- `veblen 0 a = ω ^ a`.
- `veblen a` enumerates the fixed points of `veblen b` for `b < a` when `a ≠ 0`.
-/
@[pp_nodot]
def veblen : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  veblenWith (ω ^ ·)

@[simp]
theorem veblen_zero : veblen 0 = fun a ↦ ω ^ a := by
  rw [veblen, veblenWith_zero]

theorem veblen_zero_apply (o : Ordinal) : veblen 0 o = ω ^ o := by
  rw [veblen_zero]

theorem veblen_of_ne_zero (h : o ≠ 0) : veblen o = derivFamily fun x : Set.Iio o ↦ veblen x.1 :=
  veblenWith_of_ne_zero _ h

theorem isNormal_veblen (o : Ordinal) : IsNormal (veblen o) :=
  isNormal_veblenWith isNormal_omega0_opow o

theorem veblen_veblen_of_lt (h : a < b) (c : Ordinal) : veblen a (veblen b c) = veblen b c :=
  veblenWith_veblenWith_of_lt isNormal_omega0_opow h c

theorem veblen_succ (o : Ordinal) : veblen (Order.succ o) = deriv (veblen o) :=
  veblenWith_succ isNormal_omega0_opow o

theorem veblen_right_strictMono (o : Ordinal) : StrictMono (veblen o) :=
  veblenWith_right_strictMono isNormal_omega0_opow o

theorem veblen_right_monotone (o : Ordinal) : Monotone (veblen o) :=
  (veblen_right_strictMono o).monotone

@[simp]
theorem veblen_lt_veblen_right_iff : veblen o a < veblen o b ↔ a < b :=
  veblenWith_lt_veblenWith_right_iff isNormal_omega0_opow

@[simp]
theorem veblen_le_veblen_right_iff : veblen o a ≤ veblen o b ↔ a ≤ b :=
  veblenWith_le_veblenWith_right_iff isNormal_omega0_opow

@[simp]
theorem veblen_inj : veblen o a = veblen o b ↔ a = b :=
  veblenWith_inj isNormal_omega0_opow

theorem right_le_veblen (a b : Ordinal) : b ≤ veblen a b :=
  right_le_veblenWith isNormal_omega0_opow a b

theorem veblen_left_monotone (o : Ordinal) : Monotone fun a ↦ veblen a o :=
  veblenWith_left_monotone isNormal_omega0_opow o

@[simp]
theorem veblen_pos (a b : Ordinal) : 0 < veblen a b :=
  veblenWith_pos isNormal_omega0_opow omega0_opow_zero_pos a b

theorem veblen_zero_strictMono : StrictMono (veblen · 0) :=
  veblenWith_zero_strictMono isNormal_omega0_opow omega0_opow_zero_pos

theorem veblen_zero_monotone : Monotone (veblen · 0) :=
  veblen_zero_strictMono.monotone

@[simp]
theorem veblen_zero_lt_iff : veblen a 0 < veblen b 0 ↔ a < b :=
  veblen_zero_strictMono.lt_iff_lt

@[simp]
theorem veblen_zero_le_iff : veblen a 0 ≤ veblen b 0 ↔ a ≤ b :=
  veblen_zero_strictMono.le_iff_le

@[simp]
theorem veblen_zero_inj : veblen a 0 = veblen b 0 ↔ a = b :=
  veblen_zero_strictMono.injective.eq_iff

theorem left_le_veblen (a b : Ordinal) : a ≤ veblen a b :=
  left_le_veblenWith isNormal_omega0_opow omega0_opow_zero_pos a b

theorem isNormal_veblen_zero : IsNormal (veblen · 0) :=
  isNormal_veblenWith_zero isNormal_omega0_opow omega0_opow_zero_pos

theorem veblen_lt_veblen_iff :
    veblen a b < veblen c d ↔ a = c ∧ b < d ∨ a < c ∧ b < veblen c d ∨ c < a ∧ veblen a b < d :=
  veblenWith_lt_veblenWith_iff isNormal_omega0_opow

theorem veblen_le_veblen_iff :
    veblen a b ≤ veblen c d ↔ a = c ∧ b ≤ d ∨ a < c ∧ b ≤ veblen c d ∨ c < a ∧ veblen a b ≤ d :=
  veblenWith_le_veblenWith_iff isNormal_omega0_opow

theorem veblen_eq_veblen_iff :
    veblen a b = veblen c d ↔ a = c ∧ b = d ∨ a < c ∧ b = veblen c d ∨ c < a ∧ veblen a b = d :=
 veblenWith_eq_veblenWith_iff isNormal_omega0_opow

theorem veblen_le_veblen_of_le_of_le (ha : a ≤ c) (hb : b ≤ d) : veblen a b ≤ veblen c d := by
  rw [veblen_le_veblen_iff]
  obtain rfl | ha := ha.eq_or_lt
  · exact Or.inl ⟨rfl, hb⟩
  · exact Or.inr (Or.inl ⟨ha, hb.trans (right_le_veblen _ _)⟩)

/-! ### Epsilon function -/

/-- The epsilon function enumerates the fixed points of `ω ^ ⬝`. -/
scoped notation "ε_ " => veblen 1

/-- `ε₀` is the first fixed point of `ω ^ ⬝`, i.e. the supremum of `ω`, `ω ^ ω`, `ω ^ ω ^ ω`, … -/
scoped notation "ε₀" => ε_ 0

theorem epsilon_eq_deriv (o : Ordinal) : ε_ o = deriv (fun a ↦ ω ^ a) o := by
  rw [← succ_zero, veblen_succ, veblen_zero]

theorem epsilon0_eq_nfp : ε₀ = nfp (fun a ↦ ω ^ a) 0 := by
  rw [epsilon_eq_deriv, deriv_zero_right]

theorem epsilon_succ_eq_nfp (o : Ordinal) :
    ε_ (Order.succ o) = nfp (fun a ↦ ω ^ a) (Order.succ (ε_ o)) := by
  rw [epsilon_eq_deriv, epsilon_eq_deriv, deriv_succ]

theorem epsilon0_le_of_omega0_opow_le (h : ω ^ o ≤ o) : ε₀ ≤ o := by
  rw [epsilon0_eq_nfp]
  exact nfp_le_fp (fun _ _ ↦ (opow_le_opow_iff_right one_lt_omega0).2) (Ordinal.zero_le o) h

theorem lt_omega0_opow_of_lt_epsilon0 (h : o < ε₀) : o < ω ^ o := by
  rw [← not_le] at h ⊢
  exact mt epsilon0_le_of_omega0_opow_le h

theorem log_omega0_lt_of_lt_epsilon0 {o : Ordinal} (h0 : o ≠ 0) (ho : o < ε₀) : log ω o < o :=
  lt_log_of_lt_opow h0 (lt_omega0_opow_of_lt_epsilon0 ho)

@[simp]
theorem omega0_opow_epsilon (o : Ordinal) : ω ^ (ε_ o) = ε_ o := by
  rw [epsilon_eq_deriv, isNormal_omega0_opow.deriv_fp]

/-- `ε₀` is the limit of `0`, `ω ^ 0`, `ω ^ ω ^ 0`, … -/
theorem lt_epsilon0 : o < ε₀ ↔ ∃ n : ℕ, o < (fun a ↦ ω ^ a)^[n] 0 := by
  rw [epsilon0_eq_nfp, lt_nfp]

/-- `ω ^ ω ^ … ^ 0 < ε₀` -/
theorem iterate_omega0_opow_lt_epsilon0 (n : ℕ) : (fun a ↦ ω ^ a)^[n] 0 < ε₀ := by
  rw [lt_epsilon0]
  use n + 1
  induction n with
  | zero => simp
  | succ n IH => rwa [Function.iterate_succ_apply', Function.iterate_succ_apply',
      opow_lt_opow_iff_right one_lt_omega0]

theorem omega0_lt_epsilon (o : Ordinal) : ω < ε_ o := by
  apply lt_of_lt_of_le _ (veblen_right_monotone _ (Ordinal.zero_le o))
  simpa using iterate_omega0_opow_lt_epsilon0 2

theorem nat_lt_epsilon (n : ℕ) (o : Ordinal) : n < ε_ o :=
  (nat_lt_omega0 n).trans <| omega0_lt_epsilon o

theorem one_lt_epsilon (o : Ordinal) : 1 < ε_ o :=
  mod_cast nat_lt_epsilon 1 o

theorem epsilon_pos (o : Ordinal) : 0 < ε_ o :=
  nat_lt_epsilon 0 o

theorem isNormal_epsilon : IsNormal (veblen 1 ·) :=
  isNormal_veblen 1

theorem self_le_epsilon (o : Ordinal) : o ≤ ε_ o :=
  right_le_veblen 1 o

theorem isLimit_epsilon (o : Ordinal) : IsLimit (ε_ o) := by
  rw [← omega0_opow_epsilon]
  exact isLimit_opow_left isLimit_omega0 (epsilon_pos o).ne'

theorem principal_add_epsilon (o : Ordinal) : Principal (· + ·) (ε_ o) := by
  rw [← omega0_opow_epsilon]
  exact principal_add_omega0_opow _

theorem principal_mul_epsilon (o : Ordinal) : Principal (· * ·) (ε_ o) := by
  rw [← omega0_opow_epsilon, ← omega0_opow_epsilon]
  exact principal_mul_omega0_opow_opow _

theorem principal_opow_epsilon (o : Ordinal) : Principal (· ^ ·) (ε_ o) := by
  refine fun a b ha hb ↦ (opow_le_opow_left b (right_le_opow a one_lt_omega0)).trans_lt ?_
  rw [← opow_mul, ← omega0_opow_epsilon, opow_lt_opow_iff_right one_lt_omega0]
  exact principal_mul_epsilon o ha hb

theorem omega0_le_veblen {a b : Ordinal} (h : a ≠ 0 ∨ b ≠ 0) : ω ≤ veblen a b := by
  rw [← Ordinal.one_le_iff_ne_zero, ← Ordinal.one_le_iff_ne_zero] at h
  obtain ha | hb := h
  · apply (omega0_lt_epsilon 0).le.trans
    simpa using veblen_le_veblen_of_le_of_le ha (Ordinal.zero_le b)
  · simpa using veblen_le_veblen_of_le_of_le (Ordinal.zero_le a) hb

/-! ### Gamma function -/

/-- The gamma function enumerates the fixed points of `veblen · 0`.

Of particular importance is `Γ₀ = gamma 0`, the Feferman-Schütte ordinal. -/
def gamma (o : Ordinal) : Ordinal :=
  deriv (veblen · 0) o

@[inherit_doc]
scoped notation "Γ_ " => gamma

/-- The Feferman-Schütte ordinal `Γ₀` is the smallest fixed point of `veblen · 0`, i.e. the supremum
of `veblen ε₀ 0`, `veblen (veblen ε₀ 0) 0`, etc. -/
scoped notation "Γ₀" => Γ_ 0

theorem isNormal_gamma : IsNormal gamma :=
  isNormal_deriv _

theorem strictMono_gamma : StrictMono gamma :=
  isNormal_gamma.strictMono

theorem monotone_gamma : Monotone gamma :=
  isNormal_gamma.monotone

@[simp]
theorem gamma_lt_gamma : Γ_ a < Γ_ b ↔ a < b :=
  strictMono_gamma.lt_iff_lt

@[simp]
theorem gamma_le_gamma : Γ_ a ≤ Γ_ b ↔ a ≤ b :=
  strictMono_gamma.le_iff_le

@[simp]
theorem gamma_inj : Γ_ a = Γ_ b ↔ a = b :=
  strictMono_gamma.injective.eq_iff

theorem self_le_gamma (o : Ordinal) : o ≤ Γ_ o :=
  strictMono_gamma.le_apply

@[simp]
theorem veblen_gamma_zero (o : Ordinal) : veblen (Γ_ o) 0 = Γ_ o :=
  isNormal_veblen_zero.deriv_fp o

theorem gamma0_eq_nfp : Γ₀ = nfp (veblen · 0) 0 :=
  deriv_zero_right _

theorem gamma_succ_eq_nfp (o : Ordinal) :
    Γ_ (Order.succ o) = nfp (veblen · 0) (Order.succ (Γ_ o)) :=
  deriv_succ _ _

theorem gamma_limit_eq_nfp {o : Ordinal} (h : IsLimit o) :
    Γ_ o = ⨆ a : Set.Iio o, Γ_ a :=
  deriv_limit _ h

theorem gamma0_le_of_veblen_le (h : veblen o 0 ≤ o) : Γ₀ ≤ o := by
  rw [gamma0_eq_nfp]
  exact nfp_le_fp (veblen_left_monotone 0) (Ordinal.zero_le o) h

/-- `Γ₀` is the limit of `0`, `veblen 0 0`, `veblen (veblen 0 0) 0`, … -/
theorem lt_gamma0 : o < Γ₀ ↔ ∃ n : ℕ, o < (fun a ↦ veblen a 0)^[n] 0 := by
  rw [gamma0_eq_nfp, lt_nfp]

/-- `veblen (veblen … (veblen 0 0) … 0) 0 < Γ₀` -/
theorem iterate_veblen_lt_gamma0 (n : ℕ) : (fun a ↦ veblen a 0)^[n] 0 < Γ₀ := by
  rw [lt_gamma0]
  use n + 1
  induction n with
  | zero => simp
  | succ n _ => rwa [Function.iterate_succ_apply', Function.iterate_succ_apply', veblen_zero_lt_iff]

theorem epsilon0_lt_gamma (o : Ordinal) : ε₀ < Γ_ o := by
  apply lt_of_lt_of_le _ ((gamma_le_gamma.2 (Ordinal.zero_le _)))
  simpa using iterate_veblen_lt_gamma0 2

theorem omega0_lt_gamma (o : Ordinal) : ω < Γ_ o :=
  (omega0_lt_epsilon 0).trans (epsilon0_lt_gamma o)

theorem nat_lt_gamma (n : ℕ) (o : Ordinal) : n < Γ_ o :=
  (nat_lt_omega0 n).trans (omega0_lt_gamma o)

theorem one_lt_gamma (o : Ordinal) : 1 < Γ_ o :=
  mod_cast nat_lt_gamma 1 o

theorem gamma_pos (o : Ordinal) : 0 < Γ_ o :=
  nat_lt_gamma 0 o

theorem veblen_gamma_of_lt {a b : Ordinal} (h : a < Γ_ b) : veblen a (Γ_ b) = Γ_ b := by
  rw [← veblen_gamma_zero]
  exact veblen_veblen_of_lt h 0

@[simp]
theorem epsilon_gamma (o : Ordinal) : ε_ (Γ_ o) = Γ_ o :=
  veblen_gamma_of_lt (one_lt_gamma o)

theorem principal_add_gamma (o : Ordinal) : Principal (· + ·) (Γ_ o) := by
  rw [← epsilon_gamma]
  exact principal_add_epsilon _

theorem principal_mul_gamma (o : Ordinal) : Principal (· * ·) (Γ_ o) := by
  rw [← epsilon_gamma]
  exact principal_mul_epsilon _

theorem principal_opow_gamma (o : Ordinal) : Principal (· ^ ·) (Γ_ o) := by
  rw [← epsilon_gamma]
  exact principal_opow_epsilon _

theorem principal_veblen_gamma (o : Ordinal) : Principal veblen (Γ_ o) := by
  intro a b ha hb
  rwa [← veblen_gamma_of_lt ha, veblen_lt_veblen_right_iff]

/-! ### Cardinality -/

theorem card_nfp_le (f : Ordinal → Ordinal) (a : Ordinal) :
    (nfp f a).card ≤ ℵ₀ * ⨆ n, (f^[n] a).card := by
  rw [← iSup_iterate_eq_nfp]
  apply (card_iSup_le_sum_card _).trans
  simpa using (sum_le_iSup_lift _)

theorem card_nfpFamily_Iio_le {o : Ordinal.{u}} (f : Set.Iio o → Ordinal → Ordinal) (a : Ordinal) :
    (nfpFamily f a).card ≤ (max ℵ₀ o.card) * ⨆ i, (List.foldr f a i).card := by
  rw [nfpFamily, ← (equivShrink _).symm.iSup_comp]
  apply (card_iSup_le_sum_card _).trans
  apply (sum_le_iSup _).trans
  rw [(equivShrink _).symm.iSup_comp (g := fun i ↦ (List.foldr f a i).card)]
  apply mul_le_mul_right'
  rw [← Cardinal.lift_le.{u + 1}, lift_mk_shrink', lift_max, lift_aleph0]
  apply (Cardinal.lift_le.2 (mk_list_le_max _)).trans
  rw [lift_max, lift_aleph0, Ordinal.mk_Iio_ordinal, Cardinal.lift_id'.{u, u + 1}]

theorem card_veblen_le (a b : Ordinal) : (veblen a b).card ≤ max ℵ₀ (max a.card b.card) := by
  obtain rfl | ha := eq_or_ne a 0
  · simpa using card_opow_le_of_omega0_le_left le_rfl b
  · rw [veblen_of_ne_zero ha]
    refine limitRecOn b ?_ ?_ ?_
    · rw [derivFamily_zero]
      apply (card_nfpFamily_Iio_le _ _).trans
      rw [card_zero, Cardinal.max_zero_right]
      apply mul_le_left (le_max_left _ _)
      · apply ciSup_le fun i ↦ ?_
        induction i with
        | nil => simp
        | cons b i IH =>
          obtain ⟨b, hb⟩ := b
          rw [List.foldr_cons]
          exact (card_veblen_le _ _).trans <| max_le (le_max_left _ _)
            (max_le ((card_le_card hb.le).trans (le_max_right _ _)) IH)
    · intro o IH
      rw [derivFamily_succ]
      apply (card_nfpFamily_Iio_le _ _).trans (mul_le _ _ (le_max_left _ _))
      · rw [← max_assoc]
        exact le_max_left _ _
      · apply ciSup_le fun i ↦ ?_
        induction i with
        | nil =>
          rw [List.foldr_nil, card_succ, card_succ]
          apply (add_le_add_right IH _).trans
          rw [add_eq_left]
          · exact max_le_max_left _ (max_le_max_left _ (self_le_add_right _ _))
          · exact le_max_left _ _
          · exact one_le_aleph0.trans (le_max_left _ _)
        | cons b i IH =>
          obtain ⟨b, hb⟩ := b
          rw [List.foldr_cons]
          exact (card_veblen_le _ _).trans <| max_le (le_max_left _ _) (max_le
            (le_max_of_le_right (le_max_of_le_left (card_le_card hb.le))) IH)
    · intro o ho IH
      rw [derivFamily_limit _ ho]
      apply (card_iSup_Iio_le_card_mul_iSup _).trans (mul_le _ _ (le_max_left _ _))
      · rw [Cardinal.lift_id]
        exact le_max_of_le_right (le_max_right _ _)
      · have : Nonempty (Set.Iio o) := ⟨0, ho.pos⟩
        exact ciSup_le fun b ↦
          (IH _ b.2).trans (max_le_max_left _ (max_le_max_left _ (card_le_card b.2.le)))
termination_by a

theorem card_veblen {a b : Ordinal} (h : a ≠ 0 ∨ b ≠ 0) :
    (veblen a b).card = max ℵ₀ (max a.card b.card) := by
  apply (card_veblen_le a b).antisymm (max_le _ (max_le _ _))
  · rw [aleph0_le_card]
    exact omega0_le_veblen h
  · exact card_le_card (left_le_veblen a b)
  · exact card_le_card (right_le_veblen a b)

@[simp]
theorem card_epsilon (a : Ordinal) : (ε_ a).card = max ℵ₀ a.card := by
  have : card 1 ≤ ℵ₀ := by simp
  rw [card_veblen (Or.inl one_ne_zero), ← max_assoc, max_eq_left this]

/-- `ε₀` is a countable ordinal. -/
theorem card_epsilon0 : card ε₀ = ℵ₀ := by
  simp

@[simp]
theorem card_gamma (a : Ordinal) : (Γ_ a).card = max ℵ₀ a.card := by
  apply le_antisymm
  · refine limitRecOn a ?_ ?_ ?_
    · rw [card_zero, Cardinal.max_zero_right, gamma0_eq_nfp]
      apply (card_nfp_le _ _).trans (mul_le_left le_rfl (ciSup_le _))
      intro n
      induction n with
      | zero => simp
      | succ n IH =>
        rw [Function.iterate_succ_apply']
        apply (card_veblen_le _ _).trans
        rw [card_zero, Cardinal.max_zero_right, max_eq_left IH]
    · intro o IH
      rw [gamma_succ_eq_nfp]
      apply (card_nfp_le _ _).trans (mul_le (le_max_left _ _) (ciSup_le _) (le_max_left _ _))
      intro n
      induction n with
      | zero =>
        rw [Function.iterate_zero_apply, card_succ, card_succ, add_eq_left]
        · apply IH.trans
          apply max_le_max_left
          apply self_le_add_right
        · rw [aleph0_le_card]
          exact (omega0_lt_gamma o).le
        · rw [one_le_card]
          exact (one_lt_gamma o).le
      | succ n IH =>
        rw [Function.iterate_succ_apply']
        apply (card_veblen_le _ _).trans
        rw [card_zero, Cardinal.max_zero_right]
        exact max_le (le_max_left _ _) IH
    · intro o ho IH
      rw [gamma_limit_eq_nfp ho]
      apply (card_iSup_Iio_le_card_mul_iSup _).trans
      rw [Cardinal.lift_id]
      apply mul_le (le_max_right _ _) _ (le_max_left _ _)
      have : Nonempty (Set.Iio o) := ⟨0, ho.pos⟩
      exact ciSup_le fun a ↦ (IH _ a.2).trans (max_le_max_left _ (card_le_card a.2.le))
  · apply max_le _ (card_le_card (self_le_gamma a))
    rw [aleph0_le_card]
    exact (omega0_lt_gamma a).le

/-- `Γ₀` is a countable ordinal. -/
theorem card_gamma0 : card Γ₀ = ℵ₀ := by
  simp

end Ordinal
