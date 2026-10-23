module

public import AFree.MetricCurrents.MollAux3
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Lebesgue points and mollification
-/

@[expose] public section

open MeasureTheory Filter Topology Metric
open scoped NNReal

namespace AFree.MetricCurrents.Moll

open PDE AFree

variable {d : ℕ} {ρ : Vec d → ℝ}

theorem continuous_kernel_sub (hρ : IsMollifierKernel ρ) (ε : ℝ) (x : Vec d) :
    Continuous fun y => scaledKernel ρ ε (x - y) :=
  (continuous_scaledKernel hρ ε).comp (continuous_const.sub continuous_id)

theorem hasCompactSupport_kernel_sub (hρ : IsMollifierKernel ρ) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    HasCompactSupport fun y => scaledKernel ρ ε (x - y) :=
  (hasCompactSupport_scaledKernel hρ hε).comp_isClosedEmbedding
    (Homeomorph.subLeft x).isClosedEmbedding

theorem integrable_kernel_sub_mul (hρ : IsMollifierKernel ρ) {ε : ℝ} (hε : 0 < ε) {G : Vec d → ℝ}
    (hG : LocallyIntegrable G volume) (x : Vec d) :
    Integrable fun y => G y * scaledKernel ρ ε (x - y) :=
  hG.integrable_smul_right_of_hasCompactSupport (continuous_kernel_sub hρ ε x)
    (hasCompactSupport_kernel_sub hρ hε x)

theorem integral_kernel_sub (hρ : IsMollifierKernel ρ) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    ∫ y, scaledKernel ρ ε (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun z => scaledKernel ρ ε z) volume x]
  exact integral_scaledKernel hρ hε

/-- The key estimate: the mollification of `G` at `x` is close to `G x` when the averages of
`|G - G x|` over small closed balls are small. -/
theorem abs_conv_sub_le (hρ : IsMollifierKernel ρ) {ε : ℝ} (hε : 0 < ε) {G : Vec d → ℝ}
    (hG : LocallyIntegrable G volume) (x : Vec d) {M : ℝ} (hM : ∀ z, ρ z ≤ M) :
    |(∫ y, G y * scaledKernel ρ ε (x - y)) - G x| ≤
      M * 2 ^ d * ⨍ y in closedBall x ε, ‖G y - G x‖ := by
  have hint := integrable_kernel_sub_mul hρ hε hG x
  have hint2 : Integrable fun y => G x * scaledKernel ρ ε (x - y) :=
    (continuous_kernel_sub hρ ε x).integrable_of_hasCompactSupport
      (hasCompactSupport_kernel_sub hρ hε x) |>.const_mul _
  have h1 : (∫ y, G y * scaledKernel ρ ε (x - y)) - G x =
      ∫ y, (G y - G x) * scaledKernel ρ ε (x - y) := by
    simp_rw [sub_mul]
    rw [integral_sub hint hint2, integral_const_mul, integral_kernel_sub hρ hε, mul_one]
  rw [h1, ← Real.norm_eq_abs]
  set B := closedBall x ε with hB
  set c : ℝ := M * (ε⁻¹) ^ d with hc
  have hBint : IntegrableOn (fun y => ‖G y - G x‖) B volume :=
    ((hG.integrableOn_isCompact (isCompact_closedBall x ε)).sub
      (integrableOn_const (isCompact_closedBall x ε).measure_lt_top.ne)).norm
  have hind : Integrable (B.indicator fun y => c * ‖G y - G x‖) := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact hBint.const_mul c
  have hM0 : 0 ≤ M := by
    have := hρ.nonneg 0
    linarith [hM 0]
  have hb : ∀ y, ‖(G y - G x) * scaledKernel ρ ε (x - y)‖ ≤
      B.indicator (fun y => c * ‖G y - G x‖) y := by
    intro y
    by_cases hz : scaledKernel ρ ε (x - y) = 0
    · rw [hz, mul_zero, norm_zero]
      exact Set.indicator_nonneg (fun y _ => mul_nonneg (mul_nonneg hM0
        (pow_nonneg (inv_nonneg.2 hε.le) _)) (norm_nonneg _)) y
    have hyB : y ∈ B := by
      have := norm_le_of_scaledKernel_ne_zero hρ hε hz
      rw [hB, mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact this
    rw [Set.indicator_of_mem hyB, norm_mul,
      Real.norm_eq_abs (scaledKernel ρ ε (x - y)),
      abs_of_nonneg (scaledKernel_nonneg hρ hε.le _), mul_comm]
    refine mul_le_mul ?_ le_rfl (norm_nonneg _) (mul_nonneg hM0
      (pow_nonneg (inv_nonneg.2 hε.le) _))
    rw [hc, scaledKernel, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (pow_nonneg (inv_nonneg.2 hε.le) _)
  refine (norm_integral_le_of_norm_le hind (Eventually.of_forall hb)).trans ?_
  rw [integral_indicator measurableSet_closedBall, integral_const_mul]
  have hvol : volume.real B = (2 * ε) ^ d := by
    rw [hB, measureReal_def, Real.volume_pi_closedBall _ hε.le]
    simp [ENNReal.toReal_ofReal (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * ε) _)]
  have hpos : volume.real B ≠ 0 := by
    rw [hvol]; positivity
  have h2 : ∫ y in B, ‖G y - G x‖ = volume.real B * ⨍ y in B, ‖G y - G x‖ := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos, one_mul]
  rw [h2, hvol, hc]
  refine le_of_eq ?_
  rw [mul_pow, inv_pow]
  field_simp

/-- At a Lebesgue point `x` of `G`, the mollifications `G * ρ_{1/(n+1)}(x)` converge to `G x`. -/
theorem tendsto_conv_of_lebesgue (hρ : IsMollifierKernel ρ) {G : Vec d → ℝ}
    (hG : LocallyIntegrable G volume) {x : Vec d}
    (hx : Tendsto (fun a => ⨍ y in a, ‖G y - G x‖ ∂volume)
      ((Besicovitch.vitaliFamily (volume : Measure (Vec d))).filterAt x) (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ y, G y * scaledKernel ρ (1 / ((n : ℝ) + 1)) (x - y)) atTop
      (𝓝 (G x)) := by
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ρ z ≤ M := exists_bound_kernel hρ
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
  have hA := (hx.comp (Besicovitch.tendsto_filterAt volume x)).comp hε
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hA' := hA.const_mul (M * 2 ^ d)
  rw [mul_zero] at hA'
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hA'
  rw [Real.norm_eq_abs]
  exact abs_conv_sub_le hρ (by positivity) hG x hM

end AFree.MetricCurrents.Moll
