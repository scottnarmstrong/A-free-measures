module

public import AFree.Paper.BD.Calculus
public import AFree.Measure.VectorIntegral
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `Eu` is symmetric

The symmetrised gradient of a BD function is a symmetric-matrix valued measure. The uniqueness
step is Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` applied with the finite measure
`|Eu|` and the density `polar_{pq} - polar_{qp}`.
-/

public section

open MeasureTheory PDE

namespace AFree

variable {d : ℕ}

/-- Coordinates of the vector integral against a test function, for the polar
density: `∫ φ polar_i d|μ| = (∫ φ dμ)_i`. -/
theorem integral_testFunction_polar {ι : Type*} [Fintype ι] {Ω : Set (Vec d)}
    (μ : VectorMeasure (Vec d) (ι → ℝ)) {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Ω φ) (i : ι) :
    ∫ x, φ x * polar μ x i ∂euclideanVariation μ = (∫ᵛ x, φ x ∂•μ) i := by
  obtain ⟨C, hC⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  exact (integral_smul_vectorMeasure_apply μ hφ.1.continuous.measurable hC i).symm

/-- If `Eu` is the symmetrised gradient of `u ∈ BD(Ω)`, then `Eu_{pq} = Eu_{qp}` as
signed measures and hence `polar Eu` is symmetric everywhere. -/
theorem isBDGradientOn_symm {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {u : Vec d → Vec d}
    {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)} (hEu : IsBDGradientOn Ω u Eu) :
    (∀ p q : Fin d, coordMeasure Eu (p, q) = coordMeasure Eu (q, p)) ∧
      ∀ (x : Vec d) (p q : Fin d), polar Eu x (p, q) = polar Eu x (q, p) := by
  have hmeas : ∀ p q : Fin d, ∀ᵐ x ∂euclideanVariation Eu, polar Eu x (p, q) = polar Eu x (q, p) := by
    intro p q
    have hint : Integrable (fun x => polar Eu x (p, q) - polar Eu x (q, p))
        (euclideanVariation Eu) :=
      (integrable_polar_apply Eu (p, q)).sub (integrable_polar_apply Eu (q, p))
    have h0 := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hint.locallyIntegrable.locallyIntegrableOn Ω)
      (fun g hg hc hs => by
        have hT : IsTestFunctionOn Ω g := ⟨hg, hc, hs⟩
        have hgi : ∀ r, Integrable (fun x => g x * polar Eu x r) (euclideanVariation Eu) := fun r => by
          obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hc
          exact (integrable_polar_apply Eu r).bdd_mul hg.continuous.aestronglyMeasurable
            (Filter.Eventually.of_forall hC)
        simp only [smul_eq_mul, mul_sub]
        rw [integral_sub (hgi _) (hgi _), integral_testFunction_polar Eu hT,
          integral_testFunction_polar Eu hT, BD.integral_eq_of_isBDGradientOn hEu hT p q,
          BD.integral_eq_of_isBDGradientOn hEu hT q p, sub_eq_zero, add_comm])
    have hout : ∀ᵐ x ∂euclideanVariation Eu, x ∈ Ω := by
      have := measure_eq_zero_iff_ae_notMem.1 hEu.2.1
      filter_upwards [this] with x hx
      simpa using hx
    filter_upwards [h0, hout] with x h1 h2
    exact sub_eq_zero.1 (h1 h2)
  have hsym : ∀ p q : Fin d, coordMeasure Eu (p, q) = coordMeasure Eu (q, p) := by
    intro p q
    refine VectorMeasure.ext fun E hE => ?_
    rw [coordMeasure_eq_setIntegral Eu (p, q) hE, coordMeasure_eq_setIntegral Eu (q, p) hE]
    exact integral_congr_ae (ae_restrict_of_ae (hmeas p q))
  refine ⟨hsym, fun x p q => ?_⟩
  show (coordMeasure Eu (p, q)).rnDeriv (euclideanVariation Eu) x =
    (coordMeasure Eu (q, p)).rnDeriv (euclideanVariation Eu) x
  rw [hsym p q]

end AFree
