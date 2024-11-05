/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.Linarith
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Prod.Lex
import OrdinalNotation.Mathlib.Lemmas
import OrdinalNotation.Mathlib.Veblen

open Ordinal Order Ordering

/-- Recursive definition of the Veblen normal form ordinal notation. `zero` denotes the ordinal `0`,
and `vadd s a n b` is intended to refer to `veblen s a * n + b`, where `veblen` is the two-argument
Veblen function.

Comparison on `PreVeblen` is lexicographic, with `veblen s₁ a₁` and `veblen s₂ a₂` then being
compared so that `veblen s₁ a₁ < veblen s₂ a₂` iff one of the following holds:

* `s₁ < s₂` and `a₁ < veblen s₂ a₂`
* `s₁ = s₂` and `a₁ < a₂`
* `s₂ < s₁` and `veblen s₁ a₁ < a₂`

We say that `veblen s a * n + b` is a normal form `PreVeblen.NF` whenever `a, b < veblen s a` and
all of `s`, `a`, and `b` are normal forms. `Veblen` is the subtype of normal forms. -/
inductive PreVeblen : Type
  /-- The ordinal `0` -/
  | zero : PreVeblen
  /-- The ordinal `vadd s a n b = veblen s a * n + b` -/
  | vadd : PreVeblen → PreVeblen → ℕ+ → PreVeblen → PreVeblen
  deriving DecidableEq

attribute [pp_nodot] PreVeblen.vadd

compile_inductive% PreVeblen

namespace PreVeblen

variable {s a b : PreVeblen} {n : ℕ+}

theorem one_le_sizeOf : ∀ x : PreVeblen, 1 ≤ sizeOf x
  | zero => le_rfl
  | vadd _ _ _ _ => by
    change 1 ≤ 1 + _ + _ + _
    simp_rw [add_assoc]
    exact Nat.le_add_right _ _

/-- The ordinal `0` is represented as `zero`. -/
instance : Zero PreVeblen :=
  ⟨zero⟩

@[simp]
theorem zero_def : zero = 0 :=
  rfl

instance : Inhabited PreVeblen :=
  ⟨0⟩

theorem vadd_ne_zero : vadd s a n b ≠ 0 := fun h ↦ by
  contradiction

/-- The ordinal `1` is represented as `vadd 0 0 1 0 = veblen 0 0 * 1 + 0`. -/
instance : One PreVeblen :=
  ⟨vadd 0 0 1 0⟩

@[simp]
theorem one_def : vadd 0 0 1 0 = 1 :=
  rfl

instance : NeZero (1 : PreVeblen) :=
  ⟨vadd_ne_zero⟩

/-- The ordinal `ω` is represented as `vadd 0 1 1 0 = veblen 0 1 * 1 + 0`. -/
def omega : PreVeblen :=
  vadd 0 1 1 0

/-- The ordinal `ε₀` is represented as `vadd 1 0 1 0 = veblen 1 0 * 1 + 0`. -/
def epsilon0 : PreVeblen :=
  vadd 1 0 1 0

/-- The ordinal denoted by a notation.

This operation is non-computable, as is ordinal arithmetic in general, but it can be used to state
correctness results. -/
noncomputable def repr : PreVeblen → Ordinal.{0}
  | 0 => 0
  | vadd s a n b => veblen (repr s) (repr a) * n + repr b

@[simp] theorem repr_zero : repr 0 = 0 := rfl
@[simp] theorem repr_one : repr 1 = 1 := by simp [repr]
@[simp] theorem repr_vadd (s a n b) :
  repr (vadd s a n b) = veblen (repr s) (repr a) * n + repr b := rfl

theorem repr_vadd_one_zero : repr (vadd s a 1 0) = veblen (repr s) (repr a) := by simp
theorem repr_vadd_nat_zero : repr (vadd s a n 0) = veblen (repr s) (repr a) * n := by simp

theorem repr_lt_gamma0 : ∀ x : PreVeblen, repr x < Γ₀
  | zero => gamma_pos 0
  | vadd s a n b => by
    apply principal_add_gamma 0 (principal_mul_gamma 0 (principal_veblen_gamma 0 _ _) _) _
    · exact repr_lt_gamma0 s
    · exact repr_lt_gamma0 a
    · exact nat_lt_gamma n 0
    · exact repr_lt_gamma0 b

/-- Casts a natural number into a `PreVeblen` -/
instance : NatCast PreVeblen where
  natCast
  | 0 => 0
  | Nat.succ n => vadd 0 0 n.succPNat 0

@[simp] theorem natCast_zero : (0 : ℕ) = (0 : PreVeblen) := rfl
@[simp] theorem natCast_succ (n : ℕ) : n.succ = vadd 0 0 n.succPNat 0 := rfl
theorem natCast_one : (1 : ℕ) = (1 : PreVeblen) := rfl

@[simp] theorem repr_natCast (n : ℕ) : repr n = n := by cases n <;> simp

@[simp] theorem repr_ofNat (n : ℕ) [n.AtLeastTwo] :
    repr (no_index (OfNat.ofNat n)) = n :=
  repr_natCast n

theorem injective_natCast : Function.Injective (NatCast.natCast (R := PreVeblen)) := by
  intro m n h
  apply_fun repr at h
  simpa using h

@[simp]
theorem natCast_inj (m n : ℕ) : (m : PreVeblen) = n ↔ m = n :=
  injective_natCast.eq_iff

instance : Infinite PreVeblen :=
  Infinite.of_injective _ injective_natCast

/-- Print `φ(s, a) * n`, omitting the first term if `s = 0` and `a = 0`, and omitting `n` if
`n = 1` -/
private def toStringAux (s a : PreVeblen) (n : ℕ) (s' a' : String) : String :=
  if s = 0 ∧ a = 0 then toString n
  else "φ(" ++ s' ++ ", " ++ a' ++ ")" ++ if n = 1 then "" else " * " ++ toString n

/-- Pretty-print a term in `PreVeblen` -/
private def toString : PreVeblen → String
  | zero => "0"
  | vadd s a n 0 => toStringAux s a n (toString s) (toString a)
  | vadd s a n b => toStringAux s a n (toString s) (toString a) ++ " + " ++ toString b

instance : ToString PreVeblen :=
  ⟨toString⟩

open Lean in
/-- Print a term in `PreVeblen` -/
private def repr' (prec : ℕ) : PreVeblen → Format
  | zero => "0"
  | vadd s a n b =>
    Repr.addAppParen
      ("vadd " ++ (repr' max_prec s) ++ " "  ++ (repr' max_prec a) ++ " " ++ Nat.repr (n : ℕ) ++
        " " ++ (repr' max_prec b)) prec

instance : Repr PreVeblen where
  reprPrec o prec := repr' prec o

/-! ### Ordering -/

@[semireducible]
def cmp : PreVeblen → PreVeblen → Ordering
  | 0, 0 => eq
  | 0, vadd _ _ _ _ => lt
  | vadd _ _ _ _, 0 => gt
  | vadd s₁ a₁ n₁ b₁, vadd s₂ a₂ n₂ b₂ =>
    have : toLex (sizeOf (vadd s₁ a₁ 1 0), sizeOf a₂) <
        toLex (sizeOf (vadd s₁ a₁ n₁ b₁), sizeOf (vadd s₂ a₂ n₂ b₂)) := by
      apply Prod.Lex.toLex_strictMono (Prod.mk_lt_mk_of_le_of_lt _ _)
      · simpa using one_le_sizeOf _
      · decreasing_tactic
    let veblenCmp : Ordering := match cmp s₁ s₂ with
      | lt => cmp a₁ (vadd s₂ a₂ 1 0)
      | eq => cmp a₁ a₂
      | gt => (cmp (vadd s₁ a₁ 1 0) a₂).swap
    veblenCmp.then ((_root_.cmp n₁ n₂).then (cmp b₁ b₂))
termination_by x y => toLex (sizeOf x, sizeOf y)
decreasing_by all_goals first | assumption | decreasing_tactic

instance : LT PreVeblen where
  lt x y := x.cmp y = lt

theorem lt_def (x y : PreVeblen) : x < y ↔ x.cmp y = lt := Iff.rfl

instance : @DecidableRel PreVeblen (· < ·) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ = _))

instance : LE PreVeblen where
  le x y := x.cmp y ≠ gt

theorem le_def (x y : PreVeblen) : x ≤ y ↔ x.cmp y ≠ gt := Iff.rfl

instance : @DecidableRel PreVeblen (· ≤ ·) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ≠ _))

@[simp]
protected theorem zero_le (x : PreVeblen) : 0 ≤ x := by
  cases x <;> simp [le_def, PreVeblen.cmp.eq_def]

instance : OrderBot PreVeblen where
  bot := 0
  bot_le := PreVeblen.zero_le

@[simp]
protected theorem bot_eq_zero : (⊥ : PreVeblen) = 0 :=
  rfl

theorem vadd_pos : 0 < vadd s a n b := by
  rw [lt_def, PreVeblen.cmp.eq_def]

@[simp]
protected theorem not_lt_zero (x : PreVeblen) : ¬ x < 0 := by
  cases x <;> simp [lt_def, PreVeblen.cmp.eq_def]

@[simp]
protected theorem le_zero {x : PreVeblen} : x ≤ 0 ↔ x = 0 := by
  cases x <;> simp [le_def, PreVeblen.cmp.eq_def]

protected theorem zero_lt_one : (0 : PreVeblen) < 1 :=
  vadd_pos

/-! ### Normal forms -/

/-- A normal form `PreVeblen` has the form
`veblen s₁ a₁ * n₁ + veblen s₂ a₂ * n₂ + ⋯ + veblen sₖ aₖ * nₖ` where `aᵢ < veblen sᵢ aᵢ`,
`veblen s₁ a₁ > veblen s₂ a₂ > ⋯ > veblen sₖ aₖ`, and all the `sᵢ` and `aᵢ` are also in normal form.

We will essentially only be interested in normal forms, but to avoid complicating the algorithms, we
define everything over `PreVeblen` and only prove correctness with normal form as an invariant. -/
inductive NF : PreVeblen → Prop
  /-- Zero is a normal form. -/
  | zero : NF 0
  /-- `veblen s e * n + a` is a normal form when `s`, `e`, and `a` are normal forms with
  `e, a < veblen s e`. -/
  | vadd' {s a b} : NF s → NF a → (n : ℕ+) → NF b → a < vadd s a 1 0 → b < vadd s a 1 0 →
      NF (vadd s a n b)

@[nolint defLemma]
protected alias NF.vadd := NF.vadd'

theorem NF_vadd_iff : NF (vadd s a n b) ↔ NF s ∧ NF a ∧ NF b ∧
    a < vadd s a 1 0 ∧ b < vadd s a 1 0 := by
  refine ⟨?_, fun ⟨hs, ha, hb, ha', hb'⟩ ↦ hs.vadd ha n hb ha' hb'⟩
  rintro ⟨⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  assumption'

private def decidable_NF : DecidablePred NF := fun x ↦
  match x with
  | 0 => Decidable.isTrue NF.zero
  | vadd s a n b => by
    refine @decidable_of_iff _ _ NF_vadd_iff.symm ?_
    letI := decidable_NF s
    letI := decidable_NF a
    letI := decidable_NF b
    infer_instance

instance : DecidablePred NF :=
  decidable_NF

theorem NF.fst (h : NF (vadd s a n b)) : NF s := by
  rw [NF_vadd_iff] at h
  exact h.1

theorem NF.snd (h : NF (vadd s a n b)) : NF a := by
  rw [NF_vadd_iff] at h
  exact h.2.1

theorem NF.thd (h : NF (vadd s a n b)) : NF b := by
  rw [NF_vadd_iff] at h
  exact h.2.2.1

theorem NF.fst_lt_vadd (h : NF (vadd s a n b)) : a < vadd s a 1 0 := by
  rw [NF_vadd_iff] at h
  exact h.2.2.2.1

theorem NF.snd_lt_vadd (h : NF (vadd s a n b)) : b < vadd s a 1 0 := by
  rw [NF_vadd_iff] at h
  exact h.2.2.2.2

theorem NF.with_nat (h : NF (vadd s a n b)) (n') : NF (vadd s a n' b) := by
  rwa [NF_vadd_iff] at h ⊢

theorem NF_natCast (n : ℕ) : NF n := by
  cases n
  · exact NF.zero
  · exact NF.zero.vadd NF.zero _ NF.zero vadd_pos vadd_pos

theorem NF_one : NF 1 :=
  NF_natCast 1

theorem NF_omega : NF omega := by
  decide

theorem NF_epsilon0 : NF epsilon0 := by
  decide

/-! ### Veblen function -/

/-- The two-argument Veblen function.

Unlike the constructor `vadd x y 1 0`, this ensures that the output is a normal form whenever the
inputs are. -/
@[pp_nodot]
def veblen (x y : PreVeblen) : PreVeblen :=
  let z := vadd x y 1 0
  if y < z then z else y

theorem repr_veblen (x y : PreVeblen) : repr (veblen x y) = Ordinal.veblen (repr x) (repr y) := by
  rw [veblen]
  split <;> rename_i h
  · rw [repr_vadd_one_zero]
  · sorry

theorem NF.veblen {x y : PreVeblen} (hx : NF x) (hy : NF y) : NF (veblen x y) := by
  rw [PreVeblen.veblen]
  split <;> rename_i h
  · exact hx.vadd hy _ NF.zero h vadd_pos
  · exact hy

end PreVeblen
