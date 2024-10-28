import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Ordinal.Exponential

open Order

namespace Ordinal

theorem natCast_mul_omega0 {n : ℕ} (hn : 0 < n) : n * ω = ω := by
  apply (Ordinal.le_mul_right ω (mod_cast hn)).antisymm' <| le_of_forall_lt fun a ↦ ?_
  rw [lt_mul_of_limit isLimit_omega0]
  rintro ⟨m, hm, ha⟩
  obtain ⟨m, rfl⟩ := lt_omega0.1 hm
  apply ha.trans
  rw [← Ordinal.natCast_mul]
  exact nat_lt_omega0 _

theorem natCast_mul_of_isLimit {n : ℕ} (hn : 0 < n) {o : Ordinal} (ho : IsLimit o) :
    n * o = o := by
  rw [isLimit_iff_omega0_dvd] at ho
  obtain ⟨a, rfl⟩ := ho.2
  rw [← mul_assoc, natCast_mul_omega0 hn]

theorem mul_ofNat_of_isLimit (n : ℕ) [n.AtLeastTwo] {o : Ordinal} (ho : IsLimit o) :
    (no_index (OfNat.ofNat n)) * o = o :=
  natCast_mul_of_isLimit n.pos_of_neZero ho

theorem mul_natCast_add_mul_of_isLimit {a b c : Ordinal} (h : b + a = a) (hc : c.IsLimit)
    {n : ℕ} (hn : 0 < n) : (a * n + b) * c = a * c := by
  rw [add_mul_limit _ hc, mul_assoc, natCast_mul_of_isLimit hn hc]
  cases n
  · contradiction
  · rw [add_comm, Nat.cast_add, Nat.cast_one, mul_one_add, ← add_assoc, h]

theorem isLimit_omega0_opow {o : Ordinal} (ho : o ≠ 0) : IsLimit (ω ^ o) :=
  isLimit_opow_left isLimit_omega0 ho

theorem natCast_opow_omega0 {n : ℕ} (hn : 1 < n) : n ^ ω = ω := by
  apply (right_le_opow _ (mod_cast hn)).antisymm' <| le_of_forall_lt fun a ↦ ?_
  rw [lt_opow_of_limit (mod_cast hn.ne_bot) isLimit_omega0]
  rintro ⟨m, hm, ha⟩
  obtain ⟨m, rfl⟩ := lt_omega0.1 hm
  apply ha.trans
  rw [← natCast_opow]
  exact nat_lt_omega0 _

theorem natCast_opow_omega0_opow_succ {n : ℕ} (hn : 1 < n) (a : ℕ) :
    n ^ ω ^ (a + 1) = ω ^ ω ^ a := by
  rw [add_comm, pow_add, pow_one, opow_mul, natCast_opow_omega0 hn]

theorem one_add_of_isLimit {a : Ordinal} (ha : IsLimit a) : 1 + a = a :=
  one_add_of_omega0_le (omega0_le_of_isLimit ha)

theorem natCast_opow_omega0_opow_limit {n : ℕ} (hn : 1 < n) {a : Ordinal} (ha : IsLimit a) :
    n ^ ω ^ a = ω ^ ω ^ a := by
  conv_lhs => rw [← one_add_of_isLimit ha, opow_add, opow_one, opow_mul, natCast_opow_omega0 hn]

theorem one_add_omega0_opow_mul {a b : Ordinal} (ha : a ≠ 0) (hb : b ≠ 0) :
    1 + ω ^ a * b = ω ^ a * b :=
  one_add_of_omega0_le <| (left_le_opow _ ha.bot_lt).trans (Ordinal.le_mul_left _ hb.bot_lt)

theorem one_add_omega0_opow {a : Ordinal} (ha : a ≠ 0) : 1 + ω ^ a = ω ^ a :=
  by simpa using one_add_omega0_opow_mul ha one_ne_zero

theorem mul_two (a : Ordinal) : a * 2 = a + a := by
  rw [← one_add_one_eq_two, mul_add, mul_one]

theorem succ_mul_of_isLimit {a b : Ordinal} (ha : a ≠ 0) (hb : IsLimit b) : succ a * b = a * b := by
  apply (mul_le_mul_right' (le_succ a) _).antisymm'
  have : succ a ≤ a + a := add_le_add_left (Ordinal.one_le_iff_ne_zero.2 ha) _
  apply (mul_le_mul_right' (add_le_add_left (Ordinal.one_le_iff_ne_zero.2 ha) _) _).trans
  rw [← mul_two, mul_assoc, mul_ofNat_of_isLimit _ hb]

end Ordinal

theorem PNat.one_lt_of_ne {n : ℕ+} (hn : n ≠ 1) : 1 < n := by
  rwa [ne_eq, ← PNat.le_one_iff, not_le] at hn

theorem Order.covBy_iff_lt_iff_le [LinearOrder α] {x y : α} : x ⋖ y ↔ ∀ {z}, z < y ↔ z ≤ x where
  mp := fun hx _z ↦ ⟨hx.le_of_lt, fun hz ↦ hz.trans_lt hx.lt⟩
  mpr := fun H ↦ ⟨H.2 le_rfl, fun _z hx hz ↦ (H.1 hz).not_lt hx⟩
