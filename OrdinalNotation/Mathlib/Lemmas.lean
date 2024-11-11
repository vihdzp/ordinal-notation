import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Prod.Lex

open Order Cardinal

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

theorem le_sub_of_add_le {a b c : Ordinal} (h : b + c ≤ a) : c ≤ a - b := by
  rw [← add_le_add_iff_left b]
  exact h.trans (le_add_sub a b)

theorem sub_lt_of_lt_add {a b c : Ordinal} (h : a < b + c) (hc : 0 < c) : a - b < c := by
  obtain hab | hba := lt_or_le a b
  · rwa [Ordinal.sub_eq_zero_iff_le.2 hab.le]
  · rwa [sub_lt_of_le hba]

theorem lt_add_iff {a b c : Ordinal} (hc : c ≠ 0) : a < b + c ↔ ∃ d < c, a ≤ b + d := by
  use fun h ↦ ⟨_, sub_lt_of_lt_add h hc.bot_lt, le_add_sub a b⟩
  rintro ⟨d, hd, ha⟩
  exact ha.trans_lt (add_lt_add_left hd b)

theorem self_le_omega (o : Ordinal) : o ≤ ω_ o :=
  omega_strictMono.le_apply

section principal

theorem aleph0_le_card {o} : ℵ₀ ≤ card o ↔ ω ≤ o := by
  rw [← ord_le, ord_aleph0]

-- https://github.com/leanprover-community/mathlib4/pull/18778

theorem principal_add_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : Principal (· + ·) c.ord := by
  intro a b ha hb
  rw [lt_ord, card_add] at *
  exact add_lt_of_lt hc ha hb

theorem IsInitial.principal_add {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    Principal (· + ·) o := by
  rw [← h.ord_card]
  apply principal_add_ord
  rwa [aleph0_le_card]

theorem principal_add_omega' (o : Ordinal) : Principal (· + ·) (ω_ o) :=
  (isInitial_omega o).principal_add (omega0_le_omega o)

theorem principal_mul_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : Principal (· * ·) c.ord := by
  intro a b ha hb
  rw [lt_ord, card_mul] at *
  exact mul_lt_of_lt hc ha hb

theorem IsInitial.principal_mul {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    Principal (· * ·) o := by
  rw [← h.ord_card]
  apply principal_mul_ord
  rwa [aleph0_le_card]

theorem principal_mul_omega' (o : Ordinal) : Principal (· * ·) (ω_ o) :=
  (isInitial_omega o).principal_mul (omega0_le_omega o)

end principal

-- https://github.com/leanprover-community/mathlib4/pull/18780
theorem lift_card_sInf_compl_le (s : Set Ordinal.{u}) :
    Cardinal.lift.{u + 1} (sInf sᶜ).card ≤ #s := by
  rw [← mk_Iio_ordinal]
  refine mk_le_mk_of_subset fun x (hx : x < _) ↦ ?_
  rw [← Set.not_not_mem]
  exact not_mem_of_lt_csInf' hx

end Ordinal

theorem PNat.one_lt_of_ne {n : ℕ+} (hn : n ≠ 1) : 1 < n := by
  rwa [ne_eq, ← PNat.le_one_iff, not_le] at hn

theorem Order.covBy_iff_lt_iff_le [LinearOrder α] {x y : α} : x ⋖ y ↔ ∀ z, z < y ↔ z ≤ x where
  mp := fun hx _z ↦ ⟨hx.le_of_lt, fun hz ↦ hz.trans_lt hx.lt⟩
  mpr := fun H ↦ ⟨(H _).2 le_rfl, fun _z hx hz ↦ ((H _).1 hz).not_lt hx⟩

theorem CovBy.add_one_eq [PartialOrder α] [Add α] [One α] [SuccAddOrder α] {a b : α} (h : a ⋖ b) :
    a + 1 = b := by
  rw [← succ_eq_add_one]
  exact h.succ_eq

@[simp]
theorem not_isBot_succ [LinearOrder α] [SuccOrder α] [Nontrivial α] (x : α) :
    ¬ IsBot (Order.succ x) :=
  fun h ↦ not_isMin_succ x h.isMin

@[simps!]
def PrincipalSeg.withTopCoe [Preorder α] : α <i WithTop α := by
  refine ⟨OrderEmbedding.withTopCoe.ltEmbedding, ⊤, fun x ↦ ?_⟩
  change x ∈ Set.range WithTop.some ↔ _
  rw [WithTop.range_coe]
  rfl

instance [LT α] [WellFoundedLT α] [LT β] [WellFoundedLT β] :
    WellFoundedRelation (Lex (α × β)) :=
  ⟨(· < ·), WellFounded.prod_lex wellFounded_lt wellFounded_lt⟩

theorem Prod.Lex.lt_of_le_of_lt {α β} [PartialOrder α] [LT β] {a b : α} {c d : β}
    (h₁ : a ≤ b) (h₂ : c < d) : toLex (a, c) < toLex (b, d) := by
  obtain h₁ | rfl := h₁.lt_or_eq
  · exact Prod.Lex.left _ _ h₁
  · exact Prod.Lex.right _ h₂
