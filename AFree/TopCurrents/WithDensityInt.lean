module

public import AFree.TopCurrents.Basic

/-!
# Integrals against `μ.withDensityᵥ u` (real-valued)

`∫ᵛ g d(μ.withDensityᵥ u) = ∫ g u dμ` for bounded Borel `g` and `u ∈ L¹(μ)`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

/-- `∫ᵛ g d(μ.withDensityᵥ u) = ∫ g u dμ` for bounded Borel `g` and `u ∈ L¹(μ)`. -/
theorem integral_withDensityᵥ_real {X : Type*} [MeasurableSpace X] {μ : Measure X} {u : X → ℝ}
    (hu : Integrable u μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    ∫ᵛ x, g x ∂•(μ.withDensityᵥ u) = ∫ x, g x * u x ∂μ := by
  have h1 : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (u x)) :=
    isFiniteMeasure_withDensity_ofReal hu.2
  have h2 : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (-u x)) :=
    isFiniteMeasure_withDensity_ofReal hu.neg.2
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hu]
  have hgi : ∀ (m : Measure X) [IsFiniteMeasure m], m.toSignedMeasure.Integrable g := by
    intro m _
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  rw [VectorMeasure.integral_sub_vectorMeasure (hgi _) (hgi _)]
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext; simp
  have hint : ∀ (m : Measure X) [IsFiniteMeasure m], ∫ᵛ x, g x ∂•m.toSignedMeasure = ∫ x, g x ∂m := by
    intro m _
    have := VectorMeasure.integral_toSignedMeasure (μ := m) (f := g)
    rwa [hflip] at this
  rw [hint, hint]
  have e1 : ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (u x)) =
      ∫ x, g x * max (u x) 0 ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hu.aemeasurable.ennreal_ofReal (by simp)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [mul_comm, ENNReal.toReal_ofReal', smul_eq_mul]
  have e2 : ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (-u x)) =
      ∫ x, g x * max (-u x) 0 ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (-u x))
      hu.neg.aemeasurable.ennreal_ofReal (by simp)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [mul_comm, ENNReal.toReal_ofReal', smul_eq_mul]
  have hb : ∀ v : X → ℝ, Integrable v μ → Integrable (fun x => g x * v x) μ := fun v hv =>
    hv.bdd_mul hg.aestronglyMeasurable (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  rw [e1, e2, ← integral_sub (hb _ hu.pos_part) (hb _ hu.neg_part)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [← mul_sub]
  congr 1
  rcases le_total 0 (u x) with h | h <;> simp [h]

end AFree
