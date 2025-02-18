import Mathlib.Data.List.Lex

-- This hack gets the `List.instLE` instance from core working again.
-- https://github.com/leanprover-community/mathlib4/pull/21339
section Hack
variable {α : Type*}

instance (priority := 1100) List.instLE' [LT α] : LE (List α) := ⟨List.le⟩
instance (priority := 1100) List.instLT' [LT α] : LT (List α) := ⟨List.lt⟩

instance [Preorder α] : @Std.Irrefl α (· < ·) := ⟨lt_irrefl⟩
instance [Preorder α] : @Std.Asymm α (· < ·) := ⟨fun _ _ ↦ lt_asymm⟩
instance [LinearOrder α] : @Std.Antisymm α (¬ · < ·) :=
  ⟨by simpa using fun _ _ ↦ ge_antisymm⟩
instance [LinearOrder α] : @Trans α α α (¬ · < ·) (¬ · < ·) (¬ · < ·) :=
  ⟨by simp; exact fun h₁ h₂ ↦ le_trans h₂ h₁⟩
instance [LinearOrder α] : @Std.Total α (¬ · < ·) :=
  ⟨by simpa using fun _ _ ↦ le_total _ _⟩

instance (priority := 1100) [LinearOrder α] : LinearOrder (List α) where
  le_refl := List.lex_irrefl lt_irrefl
  le_trans _ _ _ := List.le_trans
  le_total := List.le_total
  le_antisymm _ _ := List.le_antisymm
  decidableLE := inferInstanceAs (DecidableRel (¬ · > ·))
  lt_iff_le_not_le a b := by simpa [← not_le] using List.le_of_lt (α := α)
  max a b := if a ≤ b then b else a
  min a b := if a ≤ b then a else b

end Hack
