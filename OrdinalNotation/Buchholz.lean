import Mathlib.SetTheory.Cardinal.Aleph

noncomputable section

open Cardinal Set

namespace Ordinal

-- https://github.com/leanprover-community/mathlib4/pull/18542
theorem omega_pos' (o : Ordinal) : 0 < ω_ o :=
  omega0_pos.trans_le (omega0_le_omega o)

namespace Buchholz

variable {v w x y a : Ordinal}

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

theorem Omega_pos (v : Ordinal) : 0 < Ω_ v := by
  obtain rfl | h := eq_or_ne v 0
  · simp
  · rw [Omega_of_ne_zero h]
    exact omega_pos' v

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

/-- An induction principle for `CSet`. -/
@[elab_as_elim]
theorem CSet.inductionOn {p : ∀ o, o ∈ CSet v a → Prop} (ho : o ∈ CSet v a)
    (lt_Omega : ∀ x (h : x < Ω_ v), p x (CSet.lt_Omega h a))
    (add_mem : ∀ x y (hx : x ∈ CSet v a) (hy : y ∈ CSet v a), p x hx → p y hy →
      p (x + y) (CSet.add_mem hx hy))
    (buchholz_mem : ∀ w x (hw : w ∈ CSet v a) (hx : x ∈ CSet v a) (ha : x < a),
      p w hw → p x hx → p (buchholz w x) (CSet.buchholz_mem hw hx ha)) : p o ho :=
  CSet'.recOn (motive := p) _ @lt_Omega @add_mem @buchholz_mem

theorem card_le_of_mem_cSet (h : o ∈ CSet v a) : o.card ≤ ℵ_ v :=
  sorry

theorem buchholz_not_mem_cSet (v a : Ordinal) : buchholz v a ∉ CSet v a := by
  rw [buchholz_def, ← mem_compl_iff]
  refine csInf_mem ⟨ω_ (v + 1), fun h ↦ ?_⟩
  simpa using card_le_of_mem_cSet h

theorem mem_cSet_of_lt_buchholz (h : o < buchholz v a) : o ∈ CSet v a := by
  rw [buchholz_def] at h
  rw [← not_not_mem]
  exact not_mem_of_lt_csInf' h

theorem buchholz_le_of_not_mem_cSet (h : o ∉ CSet v a) : buchholz v a ≤ o := by
  contrapose! h
  exact mem_CSet_of_lt_buchholz h

end Buchholz
end Ordinal
