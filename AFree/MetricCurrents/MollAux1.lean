module

public import AFree.MetricCurrents.MollDefs

/-!
# Auxiliary facts for the mollification of Lipschitz functions: kernels and Euclidean Lipschitz
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace AFree.MetricCurrents.Moll

open PDE AFree

variable {d : ℕ}

/-- The project's standard mollifier is a mollifier kernel. -/
theorem isMollifierKernel_std (d : ℕ) : IsMollifierKernel (stdMollifier d) where
  smooth := contDiff_stdMollifier d
  compact := hasCompactSupport_stdMollifier d
  nonneg := stdMollifier_nonneg d
  integral_eq_one := integral_stdMollifier d
  tsupport_subset := by
    intro z hz
    have h := tsupport_stdMollifier_subset d hz
    have h2 : vecNormSq z < 1 ^ 2 := by simpa [euclideanBall, euclideanSqDist] using h
    have h3 : ‖z‖ ≤ vecEuclideanNorm z := norm_le_vecEuclideanNorm z
    have h4 : vecEuclideanNorm z < 1 := by
      have := vecEuclideanNorm_sq z
      nlinarith [vecEuclideanNorm_nonneg z]
    rw [mem_closedBall_zero_iff]
    linarith

section Kernel

variable {ρ : Vec d → ℝ} (hρ : IsMollifierKernel ρ)
include hρ

theorem scaledKernel_nonneg {ε : ℝ} (hε : 0 ≤ ε) (z : Vec d) : 0 ≤ scaledKernel ρ ε z :=
  mul_nonneg (pow_nonneg (inv_nonneg.2 hε) _) (hρ.nonneg _)

theorem contDiff_scaledKernel (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scaledKernel ρ ε) :=
  contDiff_const.mul (hρ.smooth.comp (contDiff_const_smul _))

theorem hasCompactSupport_scaledKernel {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (scaledKernel ρ ε) := by
  have h : HasCompactSupport fun z : Vec d => ρ (ε⁻¹ • z) := by
    have := hρ.compact.comp_isClosedEmbedding
      ((Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε.ne')).isClosedEmbedding)
    exact this
  exact h.mul_left

theorem integral_scaledKernel {ε : ℝ} (hε : 0 < ε) : ∫ z, scaledKernel ρ ε z = 1 := by
  unfold scaledKernel
  rw [integral_const_mul,
    Measure.integral_comp_smul (volume : Measure (Vec d)) ρ ε⁻¹, hρ.integral_eq_one]
  simp only [Module.finrank_fin_fun, inv_pow, inv_inv, smul_eq_mul, mul_one]
  rw [abs_of_nonneg (pow_nonneg hε.le _)]
  exact inv_mul_cancel₀ (pow_pos hε _).ne'

theorem norm_le_of_scaledKernel_ne_zero {ε : ℝ} (hε : 0 < ε) {z : Vec d}
    (hz : scaledKernel ρ ε z ≠ 0) : ‖z‖ ≤ ε := by
  have h1 : ρ (ε⁻¹ • z) ≠ 0 := by
    intro h; apply hz; simp [scaledKernel, h]
  have h2 := hρ.tsupport_subset (subset_tsupport _ h1)
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)] at h2
  rwa [inv_mul_le_iff₀ hε, mul_one] at h2

theorem continuous_scaledKernel (ε : ℝ) : Continuous (scaledKernel ρ ε) :=
  (contDiff_scaledKernel hρ ε).continuous

/-- A uniform bound for the kernel. -/
theorem exists_bound_kernel : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ρ z ≤ M := by
  obtain ⟨M, hM⟩ := hρ.smooth.continuous.bounded_above_of_compact_support hρ.compact
  exact ⟨max M 0, le_max_right _ _, fun z => ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM z)).trans (le_max_left _ _)⟩

end Kernel

/-! ### Euclidean Lipschitz functions -/

/-- Euclidean `K`-Lipschitz implies Lipschitz for the maximum metric. -/
theorem lipschitzWith_of_eucl {K : ℝ≥0} {F : Vec d → ℝ} (hF : IsEuclLipschitzWith K F) :
    LipschitzWith ⟨K * Real.sqrt d, by positivity⟩ F := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm]
  refine (hF x y).trans ?_
  show _ ≤ (K * Real.sqrt d) * _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (vecEuclideanNorm_le_sqrt_natCast_mul_norm _) K.2

theorem continuous_of_eucl {K : ℝ≥0} {F : Vec d → ℝ} (hF : IsEuclLipschitzWith K F) :
    Continuous F := (lipschitzWith_of_eucl hF).continuous

/-- At a point of differentiability, `|∂_v F| ≤ K |v|`. -/
theorem abs_fderiv_le_of_eucl {K : ℝ≥0} {F : Vec d → ℝ} (hF : IsEuclLipschitzWith K F)
    {x : Vec d} (hx : DifferentiableAt ℝ F x) (v : Vec d) :
    |fderiv ℝ F x v| ≤ K * vecEuclideanNorm v := by
  have hγ : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasDerivAt (fun t : ℝ => F (x + t • v)) (fderiv ℝ F x v) 0 := by
    have hx' : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • v) := by
      simpa using hx.hasFDerivAt
    exact hx'.comp_hasDerivAt (0 : ℝ) hγ
  have := h1.le_of_lip' (C := K * vecEuclideanNorm v)
    (mul_nonneg K.2 (vecEuclideanNorm_nonneg v))
    (Eventually.of_forall fun t => by
      simp only [zero_smul, add_zero, Real.norm_eq_abs, sub_zero]
      refine (hF _ _).trans ?_
      rw [show x + t • v - x = t • v by abel, vecEuclideanNorm_smul]
      linarith)
  simpa using this

/-- The Euclidean norm of the vector of partial derivatives is at most `K`. -/
theorem sqrt_sum_partial_sq_le {K : ℝ≥0} {F : Vec d → ℝ} (hF : IsEuclLipschitzWith K F)
    {x : Vec d} (hx : DifferentiableAt ℝ F x) :
    Real.sqrt (∑ j, partialDeriv F x j ^ 2) ≤ K := by
  set g : Vec d := fun j => partialDeriv F x j with hg
  have h1 : fderiv ℝ F x g = vecNormSq g := by
    have : g = ∑ j, g j • (Pi.single j (1 : ℝ) : Vec d) := by
      ext i; simp [Pi.single_apply]
    conv_lhs => rw [this]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, vecNormSq, vecDot]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hg, partialDeriv]
  have h2 := abs_fderiv_le_of_eucl hF hx g
  rw [h1, abs_of_nonneg (vecNormSq_nonneg g)] at h2
  have e : Real.sqrt (∑ j, partialDeriv F x j ^ 2) = vecEuclideanNorm g := by
    rw [vecEuclideanNorm, vecNormSq_eq_sum_sq]
  rw [e]
  have h3 : vecEuclideanNorm g * vecEuclideanNorm g ≤ K * vecEuclideanNorm g := by
    nlinarith [vecEuclideanNorm_sq g]
  rcases (vecEuclideanNorm_nonneg g).eq_or_lt with h0 | h0
  · rw [← h0]; exact K.2
  · exact le_of_mul_le_mul_right h3 h0

end AFree.MetricCurrents.Moll
