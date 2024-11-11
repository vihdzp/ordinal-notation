import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.W.Cardinal
import OrdinalNotation.Mathlib.Lemmas

noncomputable section

universe u

open Cardinal Set Order

namespace Ordinal

-- https://github.com/leanprover-community/mathlib4/pull/18542
theorem omega_pos' (o : Ordinal) : 0 < ω_ o :=
  omega0_pos.trans_le (omega0_le_omega o)

namespace Buchholz

variable {v w x y a b : Ordinal}

/-- An auxiliary function with `Ω_ 0 = 1` and `Ω_ v = ω_ v` otherwise. -/
def Omega (v : Ordinal) : Ordinal :=
  if v = 0 then 1 else ω_ v

@[inherit_doc]
scoped notation "Ω_ " => Omega

@[simp]
theorem Omega_zero : Ω_ 0 = 1 :=
  dif_pos rfl

theorem Omega_of_ne_zero (h : v ≠ 0) : Ω_ v = ω_ v :=
  dif_neg h

@[elab_as_elim]
def Omega_recOn {p : Ordinal → Sort*} (v : Ordinal) (h0 : p 1) (hv : ∀ v, v ≠ 0 → p (ω_ v)) :
    p (Ω_ v) :=
  if h : v = 0 then h ▸ Omega_zero ▸ h0 else Omega_of_ne_zero h ▸ hv _ h

theorem Omega_pos (v : Ordinal) : 0 < Ω_ v :=
  Omega_recOn v zero_lt_one fun v _ ↦ omega_pos' v

@[simp]
theorem Omega_succ (v : Ordinal) : Ω_ (succ v) = ω_ (succ v) :=
  Omega_of_ne_zero (succ_ne_zero v)

theorem card_Omega_le (v : Ordinal) : (Ω_ v).card ≤ ℵ_ v := by
  obtain rfl | h := eq_or_ne v 0
  · simp
  · rw [Omega_of_ne_zero h, card_omega]

theorem principal_add_Omega (v : Ordinal) : Principal (· + ·) (Ω_ v) :=
  Omega_recOn v principal_add_one fun v _ ↦ principal_add_omega' v

theorem self_le_Omega (v : Ordinal) : v ≤ Ω_ v := by
  obtain rfl | h := eq_or_ne v 0
  · simp
  · rw [Omega_of_ne_zero h]
    exact self_le_omega v

theorem Omega_le_self_iff : Ω_ v ≤ v ↔ ω_ v ≤ v := by
  obtain rfl | h := eq_or_ne v 0
  · simpa using omega0_ne_zero
  · rw [Omega_of_ne_zero h]

/-- Given a family of functions `f : Ordinal → Iio a → Ordinal`, the set `CSet' v f` represents
the closure of `Iio (Ω_ v)` under addition and application of functions in `f`.

For the definition of Buchholz's psi, `f` is the Buchholz psi function on smaller arguments. -/
private inductive CSet' (v : Ordinal) (f : Ordinal → Iio a → Ordinal) : Set Ordinal
  | lt_Omega {x : Ordinal} (h : x < Ω_ v) : CSet' v f x
  | add_mem {x y : Ordinal} (hx : x ∈ CSet' v f) (hy : y ∈ CSet' v f) : CSet' v f (x + y)
  | buchholz_mem {w x : Ordinal} (hw : w ∈ CSet' v f) (hx : x ∈ CSet' v f) (ha : x < a) :
      CSet' v f (f w ⟨x, ha⟩)

/-- Buchholz's psi functions are a family of ordinal collapsing functions. For each `v` and `x`,
`buchholz v x` is defined as the least element not in the closure of `Iio (Ω_ v)` under addition,
and the `buchholz` function itself with a smaller second argument.

Note that this is an extension of Buchholz's original psi functions, which allow the first input `v`
to be an arbitrary ordinal, whereas the original had the restriction `v ≤ ω`.

The function `buchholz 0` in particular always takes countable values, and becomes eventually
constant at a very large countable ordinal we call the **extended Buchholz ordinal**. -/
def buchholz (v a : Ordinal) : Ordinal :=
  sInf (CSet' v fun w (b : Iio a) ↦ buchholz w b.1)ᶜ
termination_by a
decreasing_by exact b.2

/-- The set `CSet v a` is defined as the closure of `Iio (Ω_ v)` under addition, and application of
`buchholz` for a second argument smaller than `a`. The value `buchholz v a` is itself defined as
the minimum excluded value of this set. -/
def CSet (v a : Ordinal) : Set Ordinal :=
  CSet' v fun w (b : Iio a) ↦ buchholz w b.1

theorem buchholz_def (v a : Ordinal) : buchholz v a = sInf (CSet v a)ᶜ := by
  rw [buchholz]
  rfl

theorem CSet.lt_Omega (h : x < Ω_ v) (a : Ordinal) : x ∈ CSet v a :=
  CSet'.lt_Omega h

theorem CSet.add_mem (hx : x ∈ CSet v a) (hy : y ∈ CSet v a) : x + y ∈ CSet v a :=
  CSet'.add_mem hx hy

theorem CSet.buchholz_mem (hw : w ∈ CSet v a) (hx : x ∈ CSet v a) (ha : x < a) :
    buchholz w x ∈ CSet v a :=
  CSet'.buchholz_mem hw hx ha

theorem CSet.zero_mem (v a : Ordinal) : 0 ∈ CSet v a :=
  CSet.lt_Omega (Omega_pos v) a

theorem CSet.mul_mem (hx : x ∈ CSet v a) : ∀ n : ℕ, x * n ∈ CSet v a
  | 0 => by simpa using CSet.zero_mem v a
  | n + 1 => by
    rw [Nat.cast_add_one, mul_add_one]
    exact CSet.add_mem (CSet.mul_mem hx n) hx

theorem CSet.mul_mem_of_lt_omega0 (hx : x ∈ CSet v a) {n : Ordinal} (hn : n < ω) :
    x * n ∈ CSet v a := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hn
  exact CSet.mul_mem hx n

/-- An induction principle for `CSet`. -/
@[elab_as_elim]
theorem CSet.induction {p : ∀ o, o ∈ CSet v a → Prop} (ho : o ∈ CSet v a)
    (lt_Omega : ∀ x (h : x < Ω_ v), p x (CSet.lt_Omega h a))
    (add_mem : ∀ x y (hx : x ∈ CSet v a) (hy : y ∈ CSet v a), p x hx → p y hy →
      p (x + y) (CSet.add_mem hx hy))
    (buchholz_mem : ∀ w x (hw : w ∈ CSet v a) (hx : x ∈ CSet v a) (ha : x < a),
      p w hw → p x hx → p (buchholz w x) (CSet.buchholz_mem hw hx ha)) : p o ho :=
  CSet'.recOn (motive := p) _ @lt_Omega @add_mem @buchholz_mem

theorem mem_cSet_of_lt_buchholz (h : o < buchholz v a) : o ∈ CSet v a := by
  rw [buchholz_def] at h
  rw [← not_not_mem]
  exact not_mem_of_lt_csInf' h

theorem buchholz_le_of_not_mem_cSet (h : o ∉ CSet v a) : buchholz v a ≤ o := by
  contrapose! h
  exact mem_cSet_of_lt_buchholz h

/-! ### Cardinality -/

/-- A W-type we surject into `CSet v a`. -/
private def W (v : Ordinal) : Type* :=
  WType <| Sum.elim (fun _ : (Ω_ v).toType ↦ Empty) (fun _ : Bool ↦ Bool)

/-- The surjection `W v → CSet v a` -/
private def WFun (v : Ordinal) : W v → Ordinal
  -- Ordinals < Ω_ v
  | .mk (Sum.inl x) _ => (enumIsoToType _).symm x
  -- Addition
  | .mk (Sum.inr false) f => WFun v (f false) + WFun v (f true)
  -- Psi
  | .mk (Sum.inr true) f => buchholz (WFun v (f false)) (WFun v (f true))

private theorem cSet_subset_range_wFun : CSet v a ⊆ range (WFun v) := by
  intro x hx
  refine CSet.induction hx ?_ ?_ ?_
  · refine fun x hx ↦ ⟨⟨Sum.inl (enumIsoToType _ ⟨x, hx⟩), nofun⟩, ?_⟩
    simp [WFun]
  · rintro _ _ _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    use ⟨Sum.inr false, Bool.rec x y⟩
    rfl
  · rintro _ _ _ _ _ ⟨w, rfl⟩ ⟨x, rfl⟩
    use ⟨Sum.inr true, Bool.rec w x⟩
    rfl

theorem mk_cSet_le (v a : Ordinal) : #(CSet v a) ≤ Cardinal.lift.{u + 1, u} (ℵ_ v) := by
  refine (mk_le_mk_of_subset cSet_subset_range_wFun).trans
    ((Cardinal.lift_id'.{u, u + 1} _ ▸ mk_range_le_lift).trans ?_)
  rw [Cardinal.lift_le]
  apply (@WType.cardinal_mk_le_max_aleph0_of_finite' _ _ ?_).trans
  · suffices (Ω_ v).card + 2 ≤ ℵ_ v by simpa [aleph0_le_aleph] using this
    have h2 := (nat_lt_aleph0 2).le
    have hv := aleph0_le_aleph v
    obtain rfl | h := eq_or_ne v 0
    · simpa
    · rwa [Omega_of_ne_zero h, card_omega, add_eq_left]
      exact h2.trans hv
  · rintro (_ | _) <;> dsimp <;> infer_instance

theorem card_buchholz_le (v a : Ordinal.{u}) : (buchholz v a).card ≤ ℵ_ v := by
  rw [buchholz_def, ← Cardinal.lift_le.{u + 1}]
  exact (lift_card_sInf_compl_le _).trans (mk_cSet_le v a)

instance (v a : Ordinal.{u}) : Small.{u} (CSet v a) := by
  rw [small_iff_lift_mk_lt_univ, Cardinal.lift_id]
  exact (mk_cSet_le v a).trans_lt (lift_lt_univ _)

private theorem nonempty_compl_cSet (v a : Ordinal) : ((CSet v a)ᶜ).Nonempty :=
  nonempty_of_not_bddAbove (not_bddAbove_compl_of_small _)

theorem buchholz_not_mem_cSet (v a : Ordinal) : buchholz v a ∉ CSet v a := by
  rw [buchholz_def, ← mem_compl_iff]
  exact csInf_mem (nonempty_compl_cSet v a)

/-! ### Basic results -/

theorem cSet_mono (v : Ordinal) : Monotone (CSet v) := by
  refine fun a b h x hx ↦ CSet.induction hx ?_ ?_ ?_
  · exact fun x hx ↦ CSet.lt_Omega hx _
  · exact fun x y _ _ ↦ CSet.add_mem
  · exact fun w x _ _ ha hw hx ↦ CSet.buchholz_mem hw hx (ha.trans_le h)

theorem buchholz_mono (v : Ordinal) : Monotone (buchholz v) := by
  intro a b h
  rw [buchholz_def, buchholz_def]
  apply csInf_le_csInf' (nonempty_compl_cSet v b)
  rw [compl_subset_compl]
  exact cSet_mono v h

theorem buchholz_lt_omega (h : v < w) (a : Ordinal) : buchholz v a < ω_ w := by
  contrapose! h
  simpa using (card_le_card h).trans (card_buchholz_le v a)

@[simp]
theorem cSet_zero (v : Ordinal) : CSet v 0 = Iio (Ω_ v) := by
  apply subset_antisymm <;> intro x hx
  · refine CSet.induction hx ?_ ?_ ?_
    · exact fun _ ↦ id
    · exact fun x y _ _ hx ↦ principal_add_Omega v hx
    · intro _ x _ _ hx
      cases Ordinal.not_lt_zero _ hx
  · exact CSet.lt_Omega hx 0

theorem Iio_Omega_subset_cSet (v a : Ordinal) : Iio (Ω_ v) ⊆ CSet v a := by
  rw [← cSet_zero]
  exact cSet_mono _ (Ordinal.zero_le a)

@[simp]
theorem buchholz_zero (v : Ordinal) : buchholz v 0 = Ω_ v := by
  rw [buchholz_def, cSet_zero, compl_Iio, csInf_Ici]

theorem Omega_le_buchholz (v a : Ordinal) : Ω_ v ≤ buchholz v a := by
  rw [← buchholz_zero]
  exact buchholz_mono v (Ordinal.zero_le a)

theorem buchholz_pos (v a : Ordinal) : 0 < buchholz v a :=
  (Omega_pos v).trans_le (Omega_le_buchholz v a)

@[simp]
theorem buchholz_ne_zero (v a : Ordinal) : buchholz v a ≠ 0 :=
  (buchholz_pos v a).ne'

theorem card_buchholz_of_ne_zero (h : v ≠ 0) (a : Ordinal) : (buchholz v a).card = ℵ_ v := by
  apply (card_buchholz_le v a).antisymm
  rw [← card_omega, ← Omega_of_ne_zero h]
  exact card_le_card (Omega_le_buchholz v a)

theorem buchholz_lt_buchholz (h : v < w) : buchholz v a < buchholz w b := by
  apply lt_of_lt_of_le _ (Omega_le_buchholz w b)
  rw [Omega_of_ne_zero h.ne_bot]
  exact buchholz_lt_omega h a

theorem buchholz_strictMono_left (a : Ordinal) : StrictMono (buchholz · a) :=
  fun _ _ ↦ buchholz_lt_buchholz

theorem buchholz_mono_left (a : Ordinal) : Monotone (buchholz · a) :=
  (buchholz_strictMono_left a).monotone

theorem buchholz_lt_of_omega_le_self (h : ω_ v ≤ v) (hw : w < v) : buchholz w a < v := by
  apply (buchholz_lt_omega (lt_succ w) _).trans_le
  rw [(self_le_omega v).le_iff_eq] at h
  rwa [← h, omega_le_omega, succ_le_iff]

theorem cSet_of_omega_le_self (h : ω_ v ≤ v) : CSet v a = Iio v := by
  rw [← Omega_le_self_iff, (self_le_Omega v).le_iff_eq] at h
  conv_rhs => rw [← h]
  obtain rfl | ha := eq_or_ne a 0
  · rw [cSet_zero]
  · apply (Iio_Omega_subset_cSet v a).antisymm'
    intro x hx
    refine CSet.induction hx ?_ ?_ ?_
    · exact fun _ ↦ id
    · exact fun x y _ _ hx ↦ principal_add_Omega v hx
    · refine fun w x _ _ _ hw _ ↦ buchholz_lt_of_omega_le_self ?_ hw
      rw [h, ← Omega_le_self_iff, h]

theorem buchholz_of_omega_le_self (h : ω_ v ≤ v) : buchholz v a = v := by
  rw [buchholz_def, cSet_of_omega_le_self h, compl_Iio, csInf_Ici]

theorem left_mem_cSet_iff : v ∈ CSet v a ↔ v < ω_ v := by
  constructor <;> intro h
  · contrapose! h
    rw [cSet_of_omega_le_self h]
    exact not_mem_Iio_self
  · obtain rfl | hv := eq_or_ne v 0
    · exact CSet.zero_mem 0 a
    · rw [← Omega_of_ne_zero hv] at h
      exact CSet.lt_Omega h a

theorem left_not_mem_cSet_iff : v ∉ CSet v a ↔ ω_ v = v := by
  rw [left_mem_cSet_iff, not_lt, (self_le_omega v).le_iff_eq]

theorem mem_cSet_limit (ha : IsLimit a) : x ∈ CSet v a ↔ ∃ b < a, x ∈ CSet v b := by
  constructor
  · intro h
    refine CSet.induction h ?_ ?_ ?_
    · exact fun x hx ↦ ⟨0, ha.pos, CSet.lt_Omega hx 0⟩
    · rintro x y _ _ ⟨b, hb, hx⟩ ⟨c, hc, hy⟩
      refine ⟨_, max_lt hb hc, CSet.add_mem ?_ ?_⟩
      · exact cSet_mono _ (le_max_left b c) hx
      · exact cSet_mono _ (le_max_right b c) hy
    · rintro w x _ _ hxa ⟨b, hb, hw⟩ ⟨c, hc, hx⟩
      obtain ⟨d, hd, hxd⟩ := (lt_limit ha).1 hxa
      refine ⟨_, max_lt (max_lt hb hc) hd, CSet.buchholz_mem ?_ ?_ ?_⟩
      · exact cSet_mono _ (le_max_of_le_left (le_max_left b c)) hw
      · exact cSet_mono _ (le_max_of_le_left (le_max_right b c)) hx
      · exact lt_max_of_lt_right hxd
  · rintro ⟨b, hb, hx⟩
    exact cSet_mono _ hb.le hx

theorem cSet_succ_of_not_mem (h : a ∉ CSet v a) : CSet v (succ a) = CSet v a := by
  apply (cSet_mono v (le_succ a)).antisymm'
  intro x hx
  refine CSet.induction hx ?_ ?_ ?_
  · exact fun y hy ↦ CSet.lt_Omega hy a
  · exact fun x y _ _ hx hy ↦ CSet.add_mem hx hy
  · intro w x _ _ ha hw hx
    rw [lt_succ_iff] at ha
    obtain ha | rfl := ha.lt_or_eq
    · exact CSet.buchholz_mem hw hx ha
    · contradiction

theorem buchholz_succ_of_not_mem (h : a ∉ CSet v a) : buchholz v (succ a) = buchholz v a := by
  rw [buchholz_def, buchholz_def, cSet_succ_of_not_mem h]

/-- `CSet v (succ a)` contains no ordinals between `buchholz v a * ω` and `ω_ (succ v)`. -/
theorem not_mem_cSet_succ_of_mem_Ico (h₁ : buchholz v a * ω ≤ x) (h₂ : x.card ≤ ℵ_ v) :
    x ∉ CSet v (succ a) := by
  intro hx
  revert h₁ h₂
  refine CSet.induction hx ?_ ?_ ?_
  · exact fun x hx h _ ↦ (h.trans_lt hx).not_le <|
      (Omega_le_buchholz v a).trans (Ordinal.le_mul_left _ omega0_pos)
  · intro x y _ _ hx hy h₁ h₂
    obtain ⟨m, hm, hx⟩ := (lt_mul_of_limit isLimit_omega0).1 <|
      not_le.1 fun h ↦ hx h ((card_le_card (le_add_right x y)).trans h₂)
    obtain ⟨n, hn, hy⟩ := (lt_mul_of_limit isLimit_omega0).1 <|
      not_le.1 fun h ↦ hy h ((card_le_card (le_add_left y x)).trans h₂)
    apply h₁.not_lt <| (add_le_add hx.le hy.le).trans_lt _
    rw [← mul_add]
    exact Ordinal.mul_lt_mul_of_pos_left (principal_add_omega0 hm hn) (buchholz_pos v a)
  · intro w x _ _ ha hw hx h₁ h₂
    rw [lt_succ_iff] at ha
    obtain h | h := lt_or_le v w
    · rw [card_buchholz_of_ne_zero h.ne_bot, aleph_le_aleph] at h₂
      exact h₂.not_lt h
    · apply ((h₁.trans (buchholz_mono w ha)).trans (buchholz_mono_left a h)).not_lt
      dsimp
      conv_lhs => rw [← mul_one (buchholz v a)]
      rw [mul_lt_mul_iff_left (buchholz_pos v a)]
      exact one_lt_omega0

theorem buchholz_mul_omega0_not_mem_cSet_succ (v a : Ordinal) :
    buchholz v a * ω ∉ CSet v (succ a) := by
  apply not_mem_cSet_succ_of_mem_Ico le_rfl
  rw [card_mul, card_omega0, mul_eq_max_of_aleph0_le_right _ le_rfl]
  · exact max_le (card_buchholz_le v a) (aleph0_le_aleph v)
  · simp

/-- The intersection `CSet v a ∩ Iio (ω_ (succ v))` is downwards-closed. -/
theorem mem_cSet_of_mem_of_le (hx : x ∈ CSet v a) (hx' : x.card ≤ ℵ_ v) (hy : y ≤ x) :
    y ∈ CSet v a := by
  revert hx
  refine limitRecOn a ?_ ?_ ?_
  · rw [cSet_zero]
    exact hy.trans_lt
  · intro a IH hx
    by_cases hv : v ∈ CSet v (succ a)
    · by_cases ha : a ∈ CSet v a
      · obtain h | h := le_or_lt (buchholz v a * ω) x
        · cases not_mem_cSet_succ_of_mem_Ico h hx' hx
        · rw [← div_add_mod y (buchholz v a)]
          apply CSet.add_mem (CSet.mul_mem_of_lt_omega0 (CSet.buchholz_mem hv _ _) _) _
          · exact cSet_mono v (le_succ a) ha
          · exact lt_succ a
          · rw [div_lt (buchholz_ne_zero v a)]
            exact hy.trans_lt h
          · exact cSet_mono v (le_succ a) <|
              mem_cSet_of_lt_buchholz (mod_lt _ (buchholz_ne_zero _ _))
      · rw [cSet_succ_of_not_mem ha] at hx ⊢
        exact IH hx
    · rw [left_not_mem_cSet_iff] at hv
      rw [cSet_of_omega_le_self hv.le] at hx ⊢
      exact hy.trans_lt hx
  · intro a ha IH hx
    obtain ⟨b, hb, hx⟩ := (mem_cSet_limit ha).1 hx
    exact cSet_mono v hb.le (IH b hb hx)

theorem lt_buchholz_of_cSet_mem (hx : x ∈ CSet v a) (hx' : x.card ≤ ℵ_ v) : x < buchholz v a := by
  contrapose! hx
  exact fun h ↦ buchholz_not_mem_cSet v a (mem_cSet_of_mem_of_le h hx' hx)

theorem principal_add_buchholz (v a : Ordinal) : Principal (· + ·) (buchholz v a) := by
  intro x y hx hy
  have := mem_cSet_of_lt_buchholz hx
  have := mem_cSet_of_lt_buchholz hy
  apply lt_buchholz_of_cSet_mem
    (CSet.add_mem (mem_cSet_of_lt_buchholz hx) (mem_cSet_of_lt_buchholz hy))
  rw [card_add]
  apply Cardinal.add_le_of_le (aleph0_le_aleph v)
  · exact (card_le_card hx.le).trans (card_buchholz_le v a)
  · exact (card_le_card hy.le).trans (card_buchholz_le v a)

end Buchholz
end Ordinal
