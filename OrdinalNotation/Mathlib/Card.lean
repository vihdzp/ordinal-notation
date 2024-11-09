import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Cardinal.Arithmetic

-- https://github.com/leanprover-community/mathlib4/pull/17813

open Cardinal

namespace Ordinal

theorem eq_nat_or_omega0_le (o : Ordinal) : (∃ n : ℕ, o = n) ∨ ω ≤ o := by
  obtain ho | ho := lt_or_le o ω
  · exact Or.inl <| lt_omega0.1 ho
  · exact Or.inr ho

@[simp]
theorem aleph0_le_card (o : Ordinal) : ℵ₀ ≤ o.card ↔ ω ≤ o := by
  rw [← ord_le, ord_aleph0]

theorem h {a : Ordinal} (ha : ω ≤ a) (b : Ordinal) :
    (a ^ b).card ≤ max a.card b.card := by
  refine limitRecOn b ?_ ?_ ?_
  · simpa using one_lt_omega0.le.trans ha
  · intro b IH
    rw [opow_succ, card_mul, card_succ, Cardinal.mul_eq_max_of_aleph0_le_right, max_comm]
    · apply (max_le_max_left _ IH).trans
      rw [← max_assoc, max_self]
      exact max_le_max_left _ le_self_add
    · rw [ne_eq, card_eq_zero, opow_eq_zero]
      rintro ⟨rfl, -⟩
      cases omega0_pos.not_le ha
    · rwa [aleph0_le_card]
  · intro b hb IH
    rw [(isNormal_opow (one_lt_omega0.trans_le ha)).apply_of_isLimit hb]
    apply (card_iSup_Iio_le_card_mul_iSup _).trans
    rw [Cardinal.lift_id, Cardinal.mul_eq_max_of_aleph0_le_right, max_comm]
    · apply max_le _ (le_max_right _ _)
      apply ciSup_le'
      intro c
      exact (IH c.1 c.2).trans (max_le_max_left _ (card_le_card c.2.le))
    · simpa using hb.pos.ne'
    · refine le_ciSup_of_le ?_ ⟨1, one_lt_omega0.trans_le <| omega0_le_of_isLimit hb⟩ ?_
      · exact Cardinal.bddAbove_of_small _
      · simpa

theorem card_opow_le_of_omega0_le_right (a : Ordinal) {b : Ordinal} (hb : ω ≤ b) :
    (a ^ b).card ≤ max a.card b.card := by
  obtain ⟨n, rfl⟩ | ha := eq_nat_or_omega0_le a
  · apply (card_le_card <| opow_le_opow_left b (nat_lt_omega0 n).le).trans <|
      (card_opow_le_of_omega0_le_left le_rfl _).trans _
    simp [hb]
  · exact card_opow_le_of_omega0_le_left ha b

theorem card_opow_eq_of_omega0_le_left {a b : Ordinal} (ha : ω ≤ a) (hb : 0 < b) :
    (a ^ b).card = max a.card b.card := by
  apply (card_opow_le_of_omega0_le_left ha b).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a hb
  · exact right_le_opow b (one_lt_omega0.trans_le ha)

theorem card_opow_eq_of_omega0_le_right {a b : Ordinal} (ha : 1 < a) (hb : ω ≤ b) :
    (a ^ b).card = max a.card b.card := by
  apply (card_opow_le_of_omega0_le_right a hb).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a (omega0_pos.trans_le hb)
  · exact right_le_opow b ha

theorem card_omega0_opow {a : Ordinal} (h : a ≠ 0) : card (ω ^ a) = max ℵ₀ a.card := by
  rw [card_opow_eq_of_omega0_le_left le_rfl h.bot_lt, card_omega0]

theorem card_opow_omega0 {a : Ordinal} (h : 1 < a) : card (a ^ ω) = max ℵ₀ a.card := by
  rw [card_opow_eq_of_omega0_le_right h le_rfl, card_omega0, max_comm]

end Ordinal
