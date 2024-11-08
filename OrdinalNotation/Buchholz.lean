import Mathlib.SetTheory.Cardinal.Aleph

noncomputable section

namespace Ordinal
namespace Buchholz

/-- An auxiliary function with `Ω_ 0 = 1` and `Ω_ v = ω_ v` otherwise. -/
noncomputable def Omega (v : Ordinal) : Ordinal :=
  if v = 0 then 1 else ω_ v

@[inherit_doc]
scoped notation "Ω_ " => Omega

@[simp]
theorem Omega_zero : Ω_ 0 = 1 :=
  dif_pos rfl

theorem Omega_of_ne_zero {v : Ordinal} (h : v ≠ 0) : Ω_ v = ω_ v :=
  dif_neg h

private inductive CSet' (v : Ordinal) {a : Ordinal} (f : Ordinal → Set.Iio a → Ordinal) :
    Set Ordinal
  | lt_Omega {x : Ordinal} (h : x < Ω_ v) : CSet' v f x
  | add_mem {x y : Ordinal} (hx : x ∈ CSet' v f) (hy : y ∈ CSet' v f) : CSet' v f (x + y)
  | buchholz_mem {w x : Ordinal} (hw : w ∈ CSet' v f) (hx : x ∈ CSet' v f) (ha : x < a) :
      CSet' v f (f w ⟨x, ha⟩)

def buchholz (v : Ordinal) (x : Ordinal) : Ordinal :=
  sInf (CSet' v fun w (b : Set.Iio x) ↦ buchholz w b.1)ᶜ
termination_by x
decreasing_by exact b.2

def CSet (v : Ordinal) (a : Ordinal) : Set Ordinal :=
  CSet' v fun w (b : Set.Iio a) ↦ buchholz w b.1

end Buchholz
end Ordinal
