module

public import AFree.MetricCurrents.MollAux1
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Mollification of Lipschitz functions: smoothness, Lipschitz bound, uniform error
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal Convolution

namespace AFree.MetricCurrents.Moll

open PDE AFree

variable {d : ℕ} {ρ : Vec d → ℝ}

theorem integrable_integrand (hρ : IsMollifierKernel ρ) {F : Vec d → ℝ} (hF : Continuous F)
    {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    Integrable (fun z => F (x - z) * scaledKernel ρ ε z) :=
  Continuous.integrable_of_hasCompactSupport
    ((hF.comp (continuous_const.sub continuous_id)).mul (continuous_scaledKernel hρ ε))
    ((hasCompactSupport_scaledKernel hρ hε).mul_left)

theorem integrable_kernel (hρ : IsMollifierKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (scaledKernel ρ ε) :=
  (continuous_scaledKernel hρ ε).integrable_of_hasCompactSupport
    (hasCompactSupport_scaledKernel hρ hε)

theorem mollLip_eq_convolution (ρ : Vec d → ℝ) (ε : ℝ) (F : Vec d → ℝ) :
    mollLip ρ ε F = fun x => (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] scaledKernel ρ ε) x := by
  funext x
  unfold mollLip convolution
  rw [← integral_sub_left_eq_self (fun z => F (x - z) * scaledKernel ρ ε z) volume x]
  simp

theorem contDiff_mollLip (hρ : IsMollifierKernel ρ) {F : Vec d → ℝ} (hF : Continuous F)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (mollLip ρ ε F) := by
  rw [mollLip_eq_convolution]
  exact (hasCompactSupport_scaledKernel hρ hε).contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hF.locallyIntegrable (contDiff_scaledKernel hρ ε)

theorem mollLip_lipschitz (hρ : IsMollifierKernel ρ) {K : ℝ≥0} {F : Vec d → ℝ}
    (hF : IsEuclLipschitzWith K F) {ε : ℝ} (hε : 0 < ε) :
    IsEuclLipschitzWith K (mollLip ρ ε F) := by
  intro x y
  have hc := continuous_of_eucl hF
  have h1 : mollLip ρ ε F x - mollLip ρ ε F y =
      ∫ z, (F (x - z) - F (y - z)) * scaledKernel ρ ε z := by
    unfold mollLip
    rw [← integral_sub (integrable_integrand hρ hc hε x) (integrable_integrand hρ hc hε y)]
    simp [sub_mul]
  rw [h1, ← Real.norm_eq_abs]
  have hb : ∀ z, ‖(F (x - z) - F (y - z)) * scaledKernel ρ ε z‖ ≤
      (K * vecEuclideanNorm (x - y)) * scaledKernel ρ ε z := by
    intro z
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (scaledKernel_nonneg hρ hε.le z)]
    refine mul_le_mul_of_nonneg_right ?_ (scaledKernel_nonneg hρ hε.le z)
    refine (hF _ _).trans (le_of_eq ?_)
    rw [show x - z - (y - z) = x - y by abel]
  refine (norm_integral_le_of_norm_le ((integrable_kernel hρ hε).const_mul _)
    (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_scaledKernel hρ hε, mul_one]

theorem abs_mollLip_sub_le (hρ : IsMollifierKernel ρ) {K : ℝ≥0} {F : Vec d → ℝ}
    (hF : IsEuclLipschitzWith K F) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    |mollLip ρ ε F x - F x| ≤ Real.sqrt d * K * ε := by
  have hc := continuous_of_eucl hF
  have h1 : mollLip ρ ε F x - F x = ∫ z, (F (x - z) - F x) * scaledKernel ρ ε z := by
    unfold mollLip
    simp_rw [sub_mul]
    rw [integral_sub (integrable_integrand hρ hc hε x)
      ((integrable_kernel hρ hε).const_mul (F x)), integral_const_mul,
      integral_scaledKernel hρ hε, mul_one]
  rw [h1, ← Real.norm_eq_abs]
  have hb : ∀ z, ‖(F (x - z) - F x) * scaledKernel ρ ε z‖ ≤
      (Real.sqrt d * K * ε) * scaledKernel ρ ε z := by
    intro z
    by_cases hz : scaledKernel ρ ε z = 0
    · simp [hz]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (scaledKernel_nonneg hρ hε.le z)]
    refine mul_le_mul_of_nonneg_right ?_ (scaledKernel_nonneg hρ hε.le z)
    have hzn := norm_le_of_scaledKernel_ne_zero hρ hε hz
    have h2 := hF (x - z) x
    rw [show x - z - x = -z by abel, vecEuclideanNorm_neg] at h2
    refine h2.trans ?_
    have h3 := vecEuclideanNorm_le_sqrt_natCast_mul_norm z
    have h4 : vecEuclideanNorm z ≤ Real.sqrt d * ε :=
      h3.trans (mul_le_mul_of_nonneg_left hzn (Real.sqrt_nonneg _))
    calc (K : ℝ) * vecEuclideanNorm z ≤ K * (Real.sqrt d * ε) :=
          mul_le_mul_of_nonneg_left h4 K.2
      _ = Real.sqrt d * K * ε := by ring
  refine (norm_integral_le_of_norm_le ((integrable_kernel hρ hε).const_mul _)
    (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_scaledKernel hρ hε, mul_one]

end AFree.MetricCurrents.Moll
