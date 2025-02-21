/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Exponential
import OrdinalNotation.Mathlib.Lemmas

/-!
# Ordinal notations

This file defines a typeclass for ordinal notations, which can be used to easily infer or define all
of the appropriate typeclasses of an initial segment of the ordinals.
-/

variable {α : Type*} {x y : α}

open Order Set

namespace Ordinal

/-! ### Notation class -/

/-- A typeclass for the first infinite ordinal `ω`.

We don't give it notation as it would clash with `Ordinal.omega0`. -/
class Omega (α : Type*) where
  /-- The first infinite ordinal `ω`. -/
  omega : α

/-- An ordinal notation is a principal segment of the ordinals with decidable ordering.

Usually, one first constructs a larger type of terms, of which a certain subtype of "normal forms"
satisfies the appropriate conditions.

As a convenient nontriviality condition, we require that an ordinal notation is able to represent
ordinals at least as big as `ω`. -/
class Notation (α : Type*) [LinearOrder α] extends Zero α, One α, Omega α where
  /-- Evalulate a term as an ordinal. This is noncomputable as ordinals have no VM representation. -/
  eval : α <i Ordinal.{0}

  eval_zero : eval 0 = 0 := by simp
  eval_one : eval 1 = 1 := by simp
  eval_omega : eval omega = ω := by simp

namespace Notation

export Omega (omega)
attribute [simp] eval_zero eval_one eval_omega

/-- Construct a linear order from a principal segment into the ordinals. -/
def linearOrderOfRepr (lt : α → α → Prop) [DecidableRel lt]
    (eval : lt ≺i (· < · : Ordinal → Ordinal → Prop)) : LinearOrder α :=
  have : IsStrictTotalOrder α lt :=
    { irrefl a := by
        rw [← eval.map_rel_iff']
        exact lt_irrefl _
      trichotomous a b := by
        rw [← eval.map_rel_iff', ← eval.inj, ← eval.map_rel_iff']
        exact lt_trichotomy _ _
      trans a b c := by
        rw [← eval.map_rel_iff', ← eval.map_rel_iff', ← eval.map_rel_iff']
        exact lt_trans }
  linearOrderOfSTO lt

variable [LinearOrder α] [Notation α]

/-- The smallest ordinal not evalesented by an ordinal notation. -/
def top (α : Type*) [LinearOrder α] [h : Notation α] : Ordinal.{0} := h.eval.top

theorem eval_strictMono : StrictMono (eval : α → _) := eval.strictMono
theorem eval_monotone : Monotone (eval : α → _) := eval.monotone
theorem eval_le_eval : eval x ≤ eval y ↔ x ≤ y := eval.le_iff_le
theorem eval_lt_eval : eval x < eval y ↔ x < y := eval.lt_iff_lt
theorem eval_inj : eval x = eval y ↔ x = y := eval.inj
theorem eval_lt_top (x : α) : eval x < top α := eval.lt_top x
theorem range_eval : range (eval : α → _) = Set.Iio (top α) := eval.range_eq_Iio_top

@[simp] theorem eval_eq_zero_iff : eval (x : α) = 0 ↔ x = 0 :=
  eval_zero (α := α) ▸ eval_inj (y := 0)
@[simp] theorem eval_eq_one_iff : eval (x : α) = 1 ↔ x = 1 :=
  eval_one (α := α) ▸ eval_inj (y := 1)

theorem eval_ne_zero_iff : eval (x : α) ≠ 0 ↔ x ≠ 0 := eval_eq_zero_iff.not
theorem eval_ne_one_iff : eval (x : α) ≠ 1 ↔ x ≠ 1 := eval_eq_one_iff.not

theorem one_le_iff_ne_zero {x : α} : 1 ≤ x ↔ x ≠ 0 := by
  rw [← eval_le_eval, eval_one, ← eval_ne_zero_iff, Ordinal.one_le_iff_ne_zero]

theorem mem_range_eval_iff_lt {o : Ordinal} : o ∈ range (eval : α → _) ↔ o < top α :=
  eval.mem_range_iff_rel' o

theorem mem_range_eval_of_le {o} {x : α} : o ≤ eval x → o ∈ Set.range (eval : α → _) :=
  eval.mem_range_of_le

theorem isSuccPrelimit_eval_iff {x : α} : IsSuccPrelimit (eval x) ↔ IsSuccPrelimit x :=
  eval.isSuccPrelimit_apply_iff

theorem isSuccLimit_eval_iff {x : α} : IsSuccLimit (eval x) ↔ IsSuccLimit x :=
  eval.isSuccLimit_apply_iff

instance : OrderBot α where
  bot := 0
  bot_le x := by
    rw [← eval_le_eval]
    exact eval_zero.trans_le (Ordinal.zero_le _)

@[simp] theorem bot_eq_zero : (⊥ : α) = 0 := rfl

-- We can use `WellFoundedLT.conditionallyCompleteLinearOrderBot` to (nonconstructibly) define
-- infima and suprema.
instance : WellFoundedLT α := eval.isWellFounded

theorem isSuccLimit_top [NoMaxOrder α] : IsSuccLimit (top α) := by
  refine ⟨(eval_lt_top 0).not_isMin, fun a ha ↦ ?_⟩
  obtain ⟨b, rfl⟩ := mem_range_eval_iff_lt.2 ha.lt
  obtain ⟨c, hc⟩ := exists_gt b
  rw [← eval_lt_eval] at hc
  exact (ha.ge_of_gt hc).not_lt (eval_lt_top c)

/-! ### Lawful operation classes -/

/-- An ordinal notation with a correct cast into naturals. -/
class LawfulNatCast (α : Type*) [LinearOrder α] [Notation α] [NatCast α] where
  eval_natCast (n : ℕ) : eval (n : α) = n
export LawfulNatCast (eval_natCast)

/-- An ordinal notation with a correct addition operation. -/
class LawfulAdd (α : Type*) [LinearOrder α] [Notation α] [Add α] where
  eval_add (a b : α) : eval (a + b) = eval a + eval b
export LawfulAdd (eval_add)

/-- An ordinal notation with a correct subtraction operation. -/
class LawfulSub (α : Type*) [LinearOrder α] [Notation α] [Sub α] where
  eval_sub (a b : α) : eval (a - b) = eval a - eval b
export LawfulSub (eval_sub)

/-- An ordinal notation with a correct multiplication operation. -/
class LawfulMul (α : Type*) [LinearOrder α] [Notation α] [Mul α] where
  eval_mul (a b : α) : eval (a * b) = eval a * eval b
export LawfulMul (eval_mul)

/-- An ordinal notation with a correct division operation. -/
class LawfulDiv (α : Type*) [LinearOrder α] [Notation α] [Div α] where
  eval_div (a b : α) : eval (a / b) = eval a / eval b
export LawfulDiv (eval_div)

/-- An ordinal notation with a correct exponentiation operation. -/
class LawfulPow (α β : Type*) [LinearOrder α] [Notation α] [LinearOrder β] [Notation β] [Pow α β] where
  eval_pow (a : α) (b : β) : eval (a ^ b) = eval a ^ eval b
export LawfulPow (eval_pow)

/-- A typeclass for the auxiliary operation on an ordinal notation which splits a term `x = y + n`
for `y` a multiple of `ω` and natural `n`. -/
class Split (α : Type*) [LinearOrder α] [Notation α] where
  /-- Returns `y` where `x = y + n`, for `y` a multiple of `ω` and natural `n`.

  This can be computed as `ω * (x / ω)`-/
  splitFst : α → α
  /-- Returns `n` where `x = y + n`, for `y` a multiple of `ω` and natural `n`. -/
  splitSnd : α → ℕ

  eval_splitFst (a : α) : eval (splitFst a) = ω * (eval a / ω)
  splitSnd_eq (a : α) : splitSnd a = eval a % ω
export Split (splitFst splitSnd eval_splitFst splitSnd_eq)

attribute [simp] eval_natCast eval_add eval_sub eval_mul eval_div eval_pow eval_splitFst

section NatCast
variable [NatCast α] [LawfulNatCast α]

@[simp]
theorem natCast_inj {m n : ℕ} : (m : α) = n ↔ m = n := by
  rw [← Nat.cast_inj (R := Ordinal), ← eval_natCast (α := α) m, ← eval_natCast (α := α) n, eval_inj]

end NatCast

section Add
variable [Add α] [LawfulAdd α]

instance : AddMonoidWithOne α where
  add_assoc a b c := by rw [← eval_inj, eval_add]; simp [add_assoc]
  zero_add a := by rw [← eval_inj]; simp
  add_zero a := by rw [← eval_inj]; simp
  nsmul := nsmulRec

instance : CanonicallyOrderedAdd α where
  exists_add_of_le {a b} h := by
    obtain ⟨c, hc⟩ := mem_range_eval_of_le (Ordinal.sub_le_self (eval b) (eval a))
    use c
    rw [← eval_inj, eval_add, hc, Ordinal.add_sub_cancel_of_le]
    simpa
  le_self_add a b := by
    rw [← eval_le_eval, eval_add]
    exact le_self_add

instance : AddLeftMono α where
  elim a b c := by rw [← eval_le_eval, ← eval_le_eval (x := a + b)]; simp
instance : AddLeftReflectLE α where
  elim a b c := by rw [← eval_le_eval, ← eval_le_eval (x := b)]; simp
instance : AddLeftStrictMono α where
  elim a b c := by rw [← eval_lt_eval, ← eval_lt_eval (x := a + b)]; simp
instance : AddLeftReflectLT α where
  elim a b c := by rw [← eval_lt_eval, ← eval_lt_eval (x := b)]; simp

instance : AddRightMono α where
  elim a b c := by
    rw [← eval_le_eval, ← eval_le_eval (x := b + a)]
    simpa [- PrincipalSeg.le_iff_le] using (add_le_add_right · _)

instance : AddRightReflectLT α where
  elim a b c := by
    rw [← eval_lt_eval, ← eval_lt_eval (x := b)]
    simpa [- PrincipalSeg.lt_iff_lt] using lt_of_add_lt_add_right

instance : NoMaxOrder α where
  exists_gt a := by
    use a + 1
    rw [← eval_lt_eval, eval_add, eval_one]
    exact lt_add_one _

/-- An ordinal notation is a `SuccOrder` setting `succ x = x + 1`. -/
instance (α : Type*) [LinearOrder α] [Notation α] [Add α] [LawfulAdd α] : SuccAddOrder α :=
  let _ : SuccOrder α := by
    refine SuccOrder.ofCore (· + 1) ?_ fun a ha ↦ (not_isMax _ ha).elim
    intro a ha b
    rw [← eval_lt_eval, ← add_one_le_iff, ← @eval_one α, ← eval_add, eval_le_eval]
  ⟨fun _ ↦ rfl⟩

@[simp]
theorem eval_succ (x : α) : eval (Order.succ x) = eval x + 1 := by
  rw [succ_eq_add_one, eval_add, eval_one]

end Add

section Sub
variable [Sub α] [LawfulSub α]

@[simp]
theorem sub_eq_zero_iff_le {a b : α} : a - b = 0 ↔ a ≤ b := by
  rw [← eval_inj]
  simp [Ordinal.sub_eq_zero_iff_le]

theorem sub_ne_zero_iff_lt {a b : α} : a - b ≠ 0 ↔ b < a := by
  simp

@[simp]
theorem sub_pos_iff_lt {a b : α} : 0 < a - b ↔ b < a := by
  rw [← eval_lt_eval]
  simp [Ordinal.pos_iff_ne_zero, Ordinal.sub_eq_zero_iff_le]

@[simp] theorem sub_zero (a : α) : a - 0 = a := by rw [← eval_inj]; simp
@[simp] theorem zero_sub (a : α) : 0 - a = 0 := by simpa using bot_le (a := a)
@[simp] theorem sub_self (a : α) : a - a = 0 := by simp

theorem add_sub_cancel_of_le [Add α] [LawfulAdd α] {a b : α} (h : a ≤ b) : a + (b - a) = b := by
  rw [← eval_inj]
  simp [Ordinal.add_sub_cancel_of_le (eval_monotone h)]

end Sub

section Mul
variable [Mul α] [LawfulMul α]

instance : MulZeroClass α where
  zero_mul a := by rw [← eval_inj]; simp
  mul_zero a := by rw [← eval_inj]; simp

instance [Add α] [LawfulAdd α] : LeftDistribClass α where
  left_distrib a b c := by rw [← eval_inj]; simp [mul_add]

end Mul

section Div
variable [Div α] [LawfulDiv α]

@[simp]
theorem zero_div (a : α) : 0 / a = 0 := by
  rw [← eval_inj]; simp

@[simp]
theorem div_zero (a : α) : a / 0 = 0 := by
  rw [← eval_inj]; simp

theorem div_eq_zero_of_lt {a b : α} (h : a < b) : a / b = 0 := by
  rw [← eval_inj, eval_div, eval_zero]
  exact Ordinal.div_eq_zero_of_lt (eval_strictMono h)

end Div

section Mod
variable [Sub α] [Mul α] [Div α]

instance [LinearOrder α] [Notation α] : Mod α where
  mod a b := a - b * (a / b)

theorem mod_def (a b : α) : a % b = a - b * (a / b) := rfl

@[simp]
theorem eval_mod [LawfulSub α] [LawfulMul α] [LawfulDiv α] (a b : α) :
    eval (a % b) = eval a % eval b := by
  simp [mod_def]

theorem div_add_mod [Add α] [LawfulAdd α] [LawfulSub α] [LawfulMul α] [LawfulDiv α] (a b : α) :
    b * (a / b) + a % b = a := by
  rw [← eval_inj]; simpa using Ordinal.div_add_mod _ _

end Mod

section Split
variable [Split α]

theorem eval_splitFst_add_splitSnd (a : α) : eval (splitFst a) + splitSnd a = eval a := by
  rw [eval_splitFst, splitSnd_eq, Ordinal.div_add_mod]

@[simp]
theorem splitFst_natCast (n : ℕ) [NatCast α] [LawfulNatCast α] : splitFst (n : α) = 0 := by
  rw [← eval_inj, eval_splitFst, eval_natCast, Ordinal.div_eq_zero_of_lt (nat_lt_omega0 n),
    mul_zero, eval_zero]

@[simp]
theorem splitSnd_natCast (n : ℕ) [NatCast α] [LawfulNatCast α] : splitSnd (n : α) = n := by
  rw [← Nat.cast_inj (R := Ordinal), splitSnd_eq, eval_natCast, nat_mod_omega0]

theorem splitFst_eq [Mul α] [LawfulMul α] [Div α] [LawfulDiv α] (a : α) :
    splitFst a = omega * (a / omega) := by
  rw [← eval_inj, eval_splitFst]; simp

theorem splitFst_add_splitSnd [Add α] [LawfulAdd α] [NatCast α] [LawfulNatCast α] (a : α) :
    splitFst a + (splitSnd a : α) = a := by
  rw [← eval_inj, eval_add, eval_natCast, eval_splitFst_add_splitSnd]

end Split

/-- An ordinal notation on `α` may be extended to `WithTop α`. -/
instance [LinearOrder α] [Notation α] : Notation (WithTop α) where
  eval := eval.withTop
  omega := (omega : α)
  eval_zero := eval_zero
  eval_one := eval_one

end Notation
end Ordinal
