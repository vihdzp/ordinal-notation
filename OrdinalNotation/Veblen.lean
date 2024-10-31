/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.Linarith
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Prod.Lex

open Ordinal Order Ordering

/-- Recursive definition of the Veblen normal form ordinal notation. `zero` denotes the ordinal `0`,
and `vadd s a n b` is intended to refer to `veblen s a * n + b`, where `veblen` is the two-argument
Veblen function.

Comparison is performed so that `veblen s₁ a₁ < veblen s₂ a₂` iff one of the following holds:

* `s₁ < s₂` and `a₁ < veblen s₂ a₂`
* `s₁ = s₂` and `a₁ < a₂`
* `s₂ < s₁` and `veblen s₁ a₁ < a₂`

If two terms have the same ordinal value, we disambiguate by their size, so that e.g.
`ε₀ < vadd 0 ε₀ 1 0`. This (hopefully?) gives us a `LinearOrder` instance on `PreVeblen`.

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

/-- The ordinal `0` is represented as `zero`. -/
instance : Zero PreVeblen :=
  ⟨zero⟩

@[simp]
theorem zero_def : zero = 0 :=
  rfl

@[simp]
theorem sizeOf_zero : sizeOf (0 : PreVeblen) = 1 :=
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

-- TODO: repr

theorem one_le_sizeOf : ∀ x : PreVeblen, 1 ≤ sizeOf x
  | zero => le_rfl
  | vadd _ _ _ _ => by
    change 1 ≤ 1 + _ + _ + _
    simp_rw [add_assoc]
    exact Nat.le_add_right _ _

instance [LT α] [WellFoundedLT α] [LT β] [WellFoundedLT β] :
    WellFoundedRelation (Lex (α × β)) :=
  ⟨(· < ·), WellFounded.prod_lex wellFounded_lt wellFounded_lt⟩

theorem Prod.Lex.lt_of_le_of_lt {α β} [PartialOrder α] [LT β] {a b : α} {c d : β}
    (h₁ : a ≤ b) (h₂ : c < d) : toLex (a, c) < toLex (b, d) := by
  obtain h₁ | rfl := h₁.lt_or_eq
  · exact Prod.Lex.left _ _ h₁
  · exact Prod.Lex.right _ h₂

def cmp : PreVeblen → PreVeblen → Ordering
  | 0, 0 => eq
  | 0, vadd _ _ _ _ => lt
  | vadd _ _ _ _, 0 => gt
  | vadd s₁ a₁ n₁ b₁, vadd s₂ a₂ n₂ b₂ =>
    let veblenCmp : Ordering := match cmp s₁ s₂ with
      | lt => if cmp a₁ (vadd s₂ a₂ 1 0) = gt then gt else lt
      | eq => cmp a₁ a₂
      | gt => if cmp (vadd s₁ a₁ 1 0) a₂ = lt then lt else gt
    veblenCmp.then ((_root_.cmp n₁ n₂).then (cmp b₁ b₂))
termination_by x y => toLex (sizeOf x, sizeOf y)
decreasing_by
on_goal 4 => {
  apply Prod.Lex.lt_of_le_of_lt
  · simpa using one_le_sizeOf _
  · decreasing_tactic }
all_goals decreasing_tactic

end PreVeblen
