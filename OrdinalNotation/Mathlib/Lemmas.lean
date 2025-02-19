import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Prod.Lex

open Order Cardinal

namespace Ordinal

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

theorem self_le_omega (o : Ordinal) : o ≤ ω_ o :=
  omega_strictMono.le_apply

theorem self_lt_mul {a b : Ordinal} (ha : 0 < a) (hb : 1 < b) : a < a * b := by
  conv_lhs => rw [← mul_one a]
  rwa [mul_lt_mul_iff_left ha]

theorem apply_le_nfp_self (f : Ordinal → Ordinal) (a : Ordinal) : f a ≤ nfp f a :=
  iterate_le_nfp f a 1

theorem isLimit_omega (o : Ordinal) : Ordinal.IsLimit (ω_ o) := by
  rw [← ord_aleph]
  exact isLimit_ord (aleph0_le_aleph _)

-- This generalizes to a multiplicative principal?
theorem mul_omega0' {a} (ha : a ≠ 0) : a * ω = ω ^ succ (log ω a) := by
  apply le_antisymm
  · have : a < ω ^ log ω a * succ (a / (ω ^ log ω a)) := by
      apply lt_mul_succ_div _ (opow_ne_zero _ omega0_ne_zero)
    apply (mul_le_mul_right' this.le _).trans
    rw [mul_assoc, opow_succ,
      mul_omega0 (succ_pos _) (isLimit_omega0.succ_lt <| div_opow_log_lt _ one_lt_omega0)]
  · rw [opow_succ]
    exact mul_le_mul_right' (opow_log_le_self ω ha) _

-- This generalizes to a multiplicative principal?
theorem mul_omega0_opow {a b} (ha : a ≠ 0) (hb : b ≠ 0) : a * ω ^ b = ω ^ (log ω a + b) := by
  have hb' := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hb)
  conv_lhs => rw [← hb']
  rw [opow_add, opow_one, ← mul_assoc, mul_omega0' ha, ← opow_add, succ_eq_add_one, add_assoc, hb']

theorem div_eq_iff {a b c : Ordinal} (hb : b ≠ 0) : a / b = c ↔ b * c ≤ a ∧ a < b * (c + 1) := by
  rw [← Ordinal.le_div hb, ← Ordinal.div_lt hb, lt_add_one_iff, ← le_antisymm_iff, eq_comm]

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
def PrincipalSeg.natCast_ordinal : ℕ <i Ordinal where
  toFun n := n
  inj' := CharZero.cast_injective
  map_rel_iff' := Nat.cast_lt
  top := .omega0
  mem_range_iff_rel' := by simp [eq_comm, Ordinal.lt_omega0]

@[simp]
theorem PrincipalSeg.natCast_ordinal_apply (n : ℕ) : PrincipalSeg.natCast_ordinal n = n :=
  rfl

@[simps!]
def PrincipalSeg.withTopCoe [Preorder α] : α <i WithTop α := by
  refine ⟨OrderEmbedding.withTopCoe.ltEmbedding, ⊤, fun x ↦ ?_⟩
  change x ∈ Set.range WithTop.some ↔ _
  rw [WithTop.range_coe]
  rfl

theorem PrincipalSeg.top_ne [Preorder α] [Preorder β] (f : α <i β) {x : α} : f.top ≠ f x :=
  (f.lt_top x).ne'

theorem PrincipalSeg.ne_top [Preorder α] [Preorder β] (f : α <i β) {x : α} : f x ≠ f.top :=
  (f.lt_top x).ne

@[simps!]
def PrincipalSeg.withTop [PartialOrder α] [LinearOrder β] [NoMaxOrder β] [SuccOrder β]
    (f : α <i β) : WithTop α <i β where
  toFun x := match x with
    | (x : α) => f x
    | ⊤ => f.top
  inj' x y := by cases x <;> cases y <;> simp [eq_comm, f.top_ne]
  map_rel_iff' {x y} := by cases x <;> cases y <;> simp [f.lt_top, le_of_lt]
  top := Order.succ f.top
  mem_range_iff_rel' x := by
    rw [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Set.mem_range, lt_succ_iff]
    refine ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨(_ | _), rfl⟩
      · rfl
      · exact (f.lt_top _).le
    · obtain h | rfl := h.lt_or_eq
      · obtain ⟨x, rfl⟩ := f.mem_range_iff_rel.2 h
        use x
      · use ⊤

@[simp]
theorem PrincipalSeg.range_eq_Iio_top [Preorder α] [Preorder β] (f : α <i β) :
    Set.range f = Set.Iio f.top := by
  ext
  exact f.mem_range_iff_rel

@[simp]
theorem PrincipalSeg.withTop_coe [PartialOrder α] [LinearOrder β] [NoMaxOrder β] [SuccOrder β]
    (f : α <i β) (x : α) : f.withTop x = f x :=
  rfl

@[simp]
theorem PrincipalSeg.withTop_of_top [PartialOrder α] [LinearOrder β] [NoMaxOrder β] [SuccOrder β]
    (f : α <i β) : f.withTop ⊤ = f.top :=
  rfl

instance [LT α] [WellFoundedLT α] [LT β] [WellFoundedLT β] :
    WellFoundedRelation (Lex (α × β)) :=
  ⟨(· < ·), WellFounded.prod_lex wellFounded_lt wellFounded_lt⟩

theorem Prod.Lex.lt_of_le_of_lt {α β} [PartialOrder α] [LT β] {a b : α} {c d : β}
    (h₁ : a ≤ b) (h₂ : c < d) : toLex (a, c) < toLex (b, d) := by
  obtain h₁ | rfl := h₁.lt_or_eq
  · exact Prod.Lex.left _ _ h₁
  · exact Prod.Lex.right _ h₂

theorem Cardinal.mul_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) :
    a * b ≤ c :=
  (mul_le_mul' h1 h2).trans <| le_of_eq <| mul_eq_self hc

instance : CanonicallyOrderedAdd Ordinal where
  le_self_add := Ordinal.le_add_right
