module

public import AFree.MetricCurrents.MollAux2
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Gradient of the mollification of a Lipschitz function
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace AFree.MetricCurrents.Moll

open PDE AFree

variable {d : ℕ} {ρ : Vec d → ℝ}

theorem ae_differentiableAt_of_eucl {K : ℝ≥0} {F : Vec d → ℝ} (hF : IsEuclLipschitzWith K F) :
    ∀ᵐ x, DifferentiableAt ℝ F x :=
  (lipschitzWith_of_eucl hF).ae_differentiableAt

theorem measurable_partialDeriv (F : Vec d → ℝ) (j : Fin d) :
    Measurable fun x => partialDeriv F x j :=
  measurable_fderiv_apply_const ℝ F _

theorem vecEuclideanNorm_single (j : Fin d) : vecEuclideanNorm (Pi.single j (1 : ℝ) : Vec d) = 1 := by
  rw [vecEuclideanNorm, vecNormSq_eq_sum_sq]
  simp [Pi.single_apply]

theorem abs_partialDeriv_le {K : ℝ≥0} {F : Vec d → ℝ} (hF : IsEuclLipschitzWith K F) {x : Vec d}
    (hx : DifferentiableAt ℝ F x) (j : Fin d) : |partialDeriv F x j| ≤ K := by
  have := abs_fderiv_le_of_eucl hF hx (Pi.single j 1)
  rwa [vecEuclideanNorm_single, mul_one] at this

/-- Almost everywhere statements are invariant under `z ↦ x - z`. -/
theorem ae_sub_left {P : Vec d → Prop} (h : ∀ᵐ y, P y) (x : Vec d) : ∀ᵐ z, P (x - z) :=
  (Measure.measurePreserving_sub_left (volume : Measure (Vec d)) x).quasiMeasurePreserving.ae h

theorem tendsto_slope_of_differentiableAt {F : Vec d → ℝ} {a : Vec d} (hx : DifferentiableAt ℝ F a)
    (v : Vec d) :
    Tendsto (fun t : ℝ => t⁻¹ * (F (a + t • v) - F a)) (𝓝[≠] 0) (𝓝 (fderiv ℝ F a v)) := by
  have hγ : HasDerivAt (fun t : ℝ => a + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
  have h1 : HasDerivAt (fun t : ℝ => F (a + t • v)) (fderiv ℝ F a v) 0 := by
    have hx' : HasFDerivAt F (fderiv ℝ F a) (a + (0 : ℝ) • v) := by
      simpa using hx.hasFDerivAt
    exact hx'.comp_hasDerivAt (0 : ℝ) hγ
  simpa using h1.tendsto_slope_zero

theorem partialDeriv_mollLip_eq (hρ : IsMollifierKernel ρ) {K : ℝ≥0} {F : Vec d → ℝ}
    (hF : IsEuclLipschitzWith K F) {ε : ℝ} (hε : 0 < ε) (x : Vec d) (j : Fin d) :
    partialDeriv (mollLip ρ ε F) x j = ∫ z, partialDeriv F (x - z) j * scaledKernel ρ ε z := by
  have hc := continuous_of_eucl hF
  set v : Vec d := Pi.single j 1 with hv
  have hG : DifferentiableAt ℝ (mollLip ρ ε F) x :=
    ((contDiff_mollLip hρ hc hε).differentiable (by simp)) x
  have hlim1 := tendsto_slope_of_differentiableAt hG v
  have hrew : ∀ t : ℝ, t⁻¹ * (mollLip ρ ε F (x + t • v) - mollLip ρ ε F x) =
      ∫ z, (t⁻¹ * (F (x - z + t • v) - F (x - z))) * scaledKernel ρ ε z := by
    intro t
    have e1 : ∀ z, (t⁻¹ * (F (x - z + t • v) - F (x - z))) * scaledKernel ρ ε z =
        t⁻¹ * (F (x + t • v - z) * scaledKernel ρ ε z - F (x - z) * scaledKernel ρ ε z) := by
      intro z
      rw [show x - z + t • v = x + t • v - z by abel]
      ring
    simp_rw [e1]
    rw [integral_const_mul, integral_sub (integrable_integrand hρ hc hε (x + t • v))
      (integrable_integrand hρ hc hε x)]
    rfl
  have hlim2 : Tendsto (fun t : ℝ => ∫ z, (t⁻¹ * (F (x - z + t • v) - F (x - z))) *
      scaledKernel ρ ε z) (𝓝[≠] 0)
      (𝓝 (∫ z, partialDeriv F (x - z) j * scaledKernel ρ ε z)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => K * scaledKernel ρ ε z) ?_ ?_ ((integrable_kernel hρ hε).const_mul _) ?_
    · refine Eventually.of_forall fun t => ?_
      have : Continuous fun z : Vec d => (t⁻¹ * (F (x - z + t • v) - F (x - z))) *
          scaledKernel ρ ε z := by
        have := continuous_scaledKernel hρ ε
        fun_prop
      exact this.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine Eventually.of_forall fun z => ?_
      have ht' : t ≠ 0 := ht
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (scaledKernel_nonneg hρ hε.le z),
        abs_mul, abs_inv]
      refine mul_le_mul_of_nonneg_right ?_ (scaledKernel_nonneg hρ hε.le z)
      have h2 := hF (x - z + t • v) (x - z)
      rw [show x - z + t • v - (x - z) = t • v by abel, vecEuclideanNorm_smul, hv,
        vecEuclideanNorm_single, mul_one] at h2
      rw [inv_mul_le_iff₀ (abs_pos.2 ht')]
      linarith
    · filter_upwards [ae_sub_left (ae_differentiableAt_of_eucl hF) x] with z hz
      exact (tendsto_slope_of_differentiableAt hz v).mul_const _
  simp_rw [hrew] at hlim1
  exact tendsto_nhds_unique hlim1 hlim2

end AFree.MetricCurrents.Moll
