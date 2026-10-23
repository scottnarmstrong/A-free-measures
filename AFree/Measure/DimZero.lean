module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# The trivial dimension

On `Vec 0` Lebesgue measure is
a Dirac mass, so every finite measure is absolutely continuous and has zero singular part.
-/

public section

open MeasureTheory PDE

namespace AFree

/-- If `d = 0`, every finite measure `σ` on `Vec 0` has `σ.singularPart volume = 0`. -/
theorem singularPart_eq_zero_dimZero (σ : Measure (Vec 0)) [IsFiniteMeasure σ] :
    σ.singularPart volume = 0 := by
  apply Measure.singularPart_eq_zero_of_ac
  intro s hs
  have hvol : (volume : Measure (Vec 0)) = Measure.dirac default := by
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) = _
    rw [Measure.pi_of_empty]
    congr 1; exact Subsingleton.elim _ _
  by_cases hne : s.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hx' : x = default := Subsingleton.elim _ _
    subst hx'
    rw [hvol, Measure.dirac_apply_of_mem hx] at hs
    exact absurd hs one_ne_zero
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp

/-- Application form: for `d = 0` and a finite measure `σ`, every property holds
almost everywhere for the singular part, since that part is zero. -/
theorem ae_singularPart_dimZero (σ : Measure (Vec 0)) [IsFiniteMeasure σ] (p : Vec 0 → Prop) :
    ∀ᵐ x ∂(σ.singularPart volume), p x := by
  rw [singularPart_eq_zero_dimZero σ]
  simp

end AFree
