module

public import AFree.Defs
public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Matrix.ChangeLinear
public import PDEFoundation.Analysis.Newtonian.Matrix.ChangeCalculus
public import PDEFoundation.Analysis.Newtonian.Potential.KernelBounds
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Convolution

/-!
# Kernel bound for `E_M` and Young's inequality

Pointwise bound on the fundamental solution `E_M` of the elliptic operator with matrix `M`, integrability of its truncation, and Young's inequality for the potential `u^M_F`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped Matrix Convolution

namespace AFree

noncomputable section

variable {d : ℕ} {Λ : ℝ} {M : Mat d}

/-- Cauchy-Schwarz for the positive semidefinite form `u ↦ vecDot u (M u)`. -/
theorem sq_vecDot_matVecMul_le (hs : M.IsSymm)
    (hnn : ∀ ξ : Vec d, 0 ≤ vecDot ξ (matVecMul M ξ)) (u v : Vec d) :
    vecDot u (matVecMul M v) ^ 2 ≤
      vecDot u (matVecMul M u) * vecDot v (matVecMul M v) := by
  have hsym : ∀ a b : Vec d, vecDot a (matVecMul M b) = vecDot b (matVecMul M a) := by
    intro a b
    have := MatChange.vecDot_matVecMul_left M b a
    rw [hs.eq] at this
    rw [vecDot_comm, ← this]
  have hbil : ∀ (t : ℝ), vecDot (u + t • v) (matVecMul M (u + t • v)) =
      vecDot u (matVecMul M u) + 2 * t * vecDot u (matVecMul M v) +
        t ^ 2 * vecDot v (matVecMul M v) := by
    intro t
    have h1 : matVecMul M (u + t • v) = matVecMul M u + t • matVecMul M v := by
      funext i; simp [matVecMul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
    rw [h1]
    have hdot : ∀ a b c : Vec d, vecDot (a + b) c = vecDot a c + vecDot b c := by
      intro a b c; simp [vecDot, add_mul, Finset.sum_add_distrib]
    have hdot2 : ∀ a b : Vec d, ∀ c : Vec d, vecDot a (b + c) = vecDot a b + vecDot a c := by
      intro a b c; simp [vecDot, mul_add, Finset.sum_add_distrib]
    have hsm : ∀ (c : ℝ) (a b : Vec d), vecDot (c • a) b = c * vecDot a b := by
      intro c a b; simp [vecDot, Finset.mul_sum, mul_assoc]
    have hsm2 : ∀ (c : ℝ) (a b : Vec d), vecDot a (c • b) = c * vecDot a b := by
      intro c a b; simp [vecDot, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hdot, hdot2, hsm, hsm2]
    rw [hsym v u]
    ring
  have hq : ∀ t : ℝ, 0 ≤ vecDot v (matVecMul M v) * t * t +
      (2 * vecDot u (matVecMul M v)) * t + vecDot u (matVecMul M u) := by
    intro t
    have := hnn (u + t • v)
    rw [hbil] at this
    nlinarith
  have hq' : ∀ t : ℝ, 0 ≤ vecDot v (matVecMul M v) * (t * t) +
      (2 * vecDot u (matVecMul M v)) * t + vecDot u (matVecMul M u) := fun t => by
    have := hq t; linarith
  have := discrim_le_zero hq'
  unfold discrim at this
  nlinarith

/-- Upper bound `|M w|² ≤ Λ w·Mw`. -/
theorem vecNormSq_matVecMul_le (hΛ : 0 < Λ) (hs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ) (w : Vec d) :
    vecNormSq (matVecMul M w) ≤ Λ * vecDot w (matVecMul M w) := by
  have hnn : ∀ ξ : Vec d, 0 ≤ vecDot ξ (matVecMul M ξ) := fun ξ =>
    le_trans (mul_nonneg (inv_nonneg.2 hΛ.le) (vecNormSq_nonneg ξ)) (hM ξ).1
  have h := sq_vecDot_matVecMul_le hs hnn w (matVecMul M w)
  have e : vecDot w (matVecMul M (matVecMul M w)) = vecNormSq (matVecMul M w) := by
    have := MatChange.vecDot_matVecMul_left M w (matVecMul M w)
    rw [hs.eq] at this
    rw [vecNormSq, ← this]
  rw [e] at h
  have h2 := (hM (matVecMul M w)).2
  set a := vecNormSq (matVecMul M w)
  set q := vecDot w (matVecMul M w)
  have ha : 0 ≤ a := vecNormSq_nonneg _
  have hq : 0 ≤ q := hnn w
  have h3 : a ^ 2 ≤ q * (Λ * a) := h.trans (mul_le_mul_of_nonneg_left h2 hq)
  rcases ha.eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hΛ.le hq
  · nlinarith

/-- The determinant of a `Λ`-elliptic matrix is at least `Λ^{-d}`. -/
theorem inv_pow_le_det (hΛ : 0 < Λ) (hs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ) :
    (Λ⁻¹) ^ d ≤ M.det := by
  have hA : M.IsHermitian := Matrix.isHermitian_iff_isSymm.2 hs
  rw [hA.det_eq_prod_eigenvalues]
  have : (Λ⁻¹) ^ d = ∏ _i : Fin d, Λ⁻¹ := by simp
  rw [this]
  simp only [RCLike.ofReal_real_eq_id, id]
  refine Finset.prod_le_prod₀ (fun _ _ => (inv_pos.2 hΛ).le) fun i _ => ?_
  set v : Vec d := ⇑(hA.eigenvectorBasis i) with hv
  have hmv : matVecMul M v = hA.eigenvalues i • v := by
    have := hA.mulVec_eigenvectorBasis i
    simpa [MatChange.matVecMul_eq_mulVec, hv] using this
  have hn : vecNormSq v = 1 := by
    have h1 : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
    rw [PiLp.norm_eq_of_L2] at h1
    have h2 : ∑ j, ‖hA.eigenvectorBasis i j‖ ^ 2 = 1 := by
      have := Real.sqrt_eq_one.1 h1
      exact this
    rw [vecNormSq_eq_sum_sq]
    simpa [hv] using h2
  have := (hM v).1
  rw [hmv, hn] at this
  have e : vecDot v (hA.eigenvalues i • v) = hA.eigenvalues i * vecNormSq v := by
    simp [vecDot, vecNormSq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, hn] at this
  simpa using this

/-- pointwise bound `|E_M(z)| ≤ K |z|^{1-d}` with
`K = Λ^{d+1} / (d |B₁|)`, for a `Λ`-elliptic `M`. -/
theorem norm_newtonKernelMat_le (hΛ : 0 < Λ) (hs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (hd : 0 < d) {z : Vec d} (hz : z ≠ 0) :
    vecEuclideanNorm (PDE.newtonKernelMat M z) ≤
      Λ ^ (d + 1) / (d * (volume (euclideanBall (0 : Vec d) 1)).toReal) *
        vecEuclideanNorm z ^ (1 - (d : ℤ)) := by
  have hdet := inv_pow_le_det hΛ hs hM
  have hdpos : 0 < M.det := lt_of_lt_of_le (by positivity) hdet
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdpos.ne')
  set w := matVecMul M⁻¹ z with hw
  have hMw : matVecMul M w = z := by
    rw [hw, MatChange.matVecMul_matVecMul, hMi, MatChange.matVecMul_one]
  have hzpos : 0 < vecEuclideanNorm z := vecEuclideanNorm_pos_iff.2 hz
  have hz2 : 0 < vecNormSq z := MatChange.vecNormSq_pos hz
  -- (a) ‖w‖ ≤ Λ‖z‖
  have hqw : vecDot w z = vecDot z w := vecDot_comm _ _
  have hwz : vecEuclideanNorm w ≤ Λ * vecEuclideanNorm z := by
    have h1 := (hM w).1
    rw [hMw] at h1
    have h2 : vecNormSq w ≤ Λ * (vecEuclideanNorm w * vecEuclideanNorm z) := by
      have := abs_vecDot_le_vecEuclideanNorm_mul w z
      have h3 : vecNormSq w ≤ Λ * vecDot w z := by
        have := mul_le_mul_of_nonneg_left h1 hΛ.le
        rwa [← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul] at this
      calc vecNormSq w ≤ Λ * vecDot w z := h3
        _ ≤ Λ * (vecEuclideanNorm w * vecEuclideanNorm z) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans this) hΛ.le
    rcases (vecEuclideanNorm_nonneg w).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · rw [← vecEuclideanNorm_sq] at h2
      nlinarith
  -- (b) q ≥ Λ⁻¹ ‖z‖²
  set q := vecDot z w with hq
  have hqe : q = vecDot w (matVecMul M w) := by
    have := MatChange.vecDot_matVecMul_left M w w
    rw [hs.eq] at this
    calc q = vecDot (matVecMul M w) w := by rw [hq, hMw]
      _ = _ := this
  have hqz : Λ⁻¹ * vecNormSq z ≤ q := by
    have h := vecNormSq_matVecMul_le hΛ hs hM w
    have h' : vecNormSq z ≤ Λ * q := by
      calc vecNormSq z = vecNormSq (matVecMul M w) := by rw [hMw]
        _ ≤ Λ * vecDot w (matVecMul M w) := h
        _ = Λ * q := by rw [hqe]
    have := mul_le_mul_of_nonneg_left h' (inv_nonneg.2 hΛ.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hΛ.ne', one_mul] at this
  have hq0 : 0 < q := lt_of_lt_of_le (mul_pos (inv_pos.2 hΛ) hz2) hqz
  -- combine denominators
  set A := Real.sqrt M.det with hA
  set B := q ^ ((d : ℝ) / 2) with hB
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 < B := Real.rpow_pos_of_pos hq0 _
  have hA2 : A ^ 2 = M.det := Real.sq_sqrt hdpos.le
  have hB2 : B ^ 2 = q ^ d := by
    rw [hB, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hAB : Λ⁻¹ ^ d * vecEuclideanNorm z ^ d ≤ A * B := by
    have hP : 0 ≤ Λ⁻¹ ^ d * vecEuclideanNorm z ^ d := by positivity
    have hlow : (Λ⁻¹ ^ d * vecEuclideanNorm z ^ d) ^ 2 ≤ (A * B) ^ 2 := by
      have h1 : Λ⁻¹ ^ d ≤ A ^ 2 := by rw [hA2]; exact hdet
      have h2 : Λ⁻¹ ^ d * (vecEuclideanNorm z ^ d) ^ 2 ≤ B ^ 2 := by
        rw [hB2, ← pow_mul, mul_comm d 2, pow_mul, ← mul_pow]
        rw [vecEuclideanNorm_sq]
        exact pow_le_pow_left₀ (by positivity) hqz d
      calc (Λ⁻¹ ^ d * vecEuclideanNorm z ^ d) ^ 2
          = Λ⁻¹ ^ d * (Λ⁻¹ ^ d * (vecEuclideanNorm z ^ d) ^ 2) := by ring
        _ ≤ A ^ 2 * B ^ 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (A * B) ^ 2 := by ring
    exact (abs_le_of_sq_le_sq' hlow (by positivity)).2
  have hD : 0 < (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    mul_pos (by exact_mod_cast hd) (volume_euclideanBall_toReal_pos _ one_pos)
  set D := (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal with hDdef
  have hE : vecEuclideanNorm (PDE.newtonKernelMat M z) = vecEuclideanNorm w / (D * A * B) := by
    unfold PDE.newtonKernelMat
    rw [vecEuclideanNorm_smul, abs_of_nonneg (by positivity)]
    simp only [← hw, ← hq, ← hDdef, ← hA, ← hB]
    ring
  rw [hE, zpow_sub₀ hzpos.ne', zpow_one, zpow_natCast]
  have hP : 0 < Λ⁻¹ ^ d * vecEuclideanNorm z ^ d := by positivity
  have hDAB : 0 < D * A * B := by
    have := lt_of_lt_of_le hP hAB
    positivity
  rw [div_le_iff₀ hDAB]
  have hΛd : Λ ^ (d + 1) * Λ⁻¹ ^ d = Λ := by
    rw [pow_succ, mul_comm (Λ ^ d) Λ, mul_assoc, ← mul_pow, mul_inv_cancel₀ hΛ.ne', one_pow,
      mul_one]
  calc vecEuclideanNorm w ≤ Λ * vecEuclideanNorm z := hwz
    _ = (Λ ^ (d + 1) * Λ⁻¹ ^ d) * vecEuclideanNorm z := by rw [hΛd]
    _ = (Λ ^ (d + 1) / D * (vecEuclideanNorm z / vecEuclideanNorm z ^ d)) *
        (D * (Λ⁻¹ ^ d * vecEuclideanNorm z ^ d)) := by
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_left hAB hD.le
      linarith

/-- The truncated kernel `Ẽ_M = E_M 1_{B_2}`. -/
def truncKernel (M : Mat d) : Vec d → Vec d :=
  Set.indicator (euclideanBall (0 : Vec d) 2) (PDE.newtonKernelMat M)

/-- The `L¹` norm `K₁ = ‖Ẽ_M‖_{L¹}` (Euclidean pointwise norm) of the truncated kernel. -/
def truncKernelNorm (M : Mat d) : ℝ :=
  ∫ z, vecEuclideanNorm (truncKernel M z)

theorem continuous_vecDot_matVecMul (A : Mat d) :
    Continuous fun z : Vec d => vecDot z (matVecMul A z) :=
  continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul ((continuous_apply i).comp (PDE.MatChange.continuous_matVecMul A))

theorem measurable_newtonKernelMat (M : Mat d) : Measurable (PDE.newtonKernelMat M) := by
  unfold PDE.newtonKernelMat
  have h1 := (PDE.MatChange.continuous_matVecMul M⁻¹).measurable
  have h2 : Measurable fun z : Vec d => (1 / ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal *
      Real.sqrt M.det * (vecDot z (matVecMul M⁻¹ z)) ^ ((d : ℝ) / 2))) :=
    measurable_const.div
      (measurable_const.mul (((continuous_vecDot_matVecMul _).measurable).pow_const _))
  exact h2.smul h1

theorem measurable_truncKernel (M : Mat d) : Measurable (truncKernel M) :=
  (measurable_newtonKernelMat M).indicator (measurableSet_euclideanBall _ _)

theorem newtonKernelMat_zero (M : Mat d) : PDE.newtonKernelMat M 0 = 0 := by
  unfold PDE.newtonKernelMat
  have : matVecMul M⁻¹ (0 : Vec d) = 0 := by funext i; simp [matVecMul]
  rw [this, smul_zero]

/-- the truncated kernel `E_M 1_{B_2}` has integrable Euclidean norm. -/
theorem integrable_vecEuclideanNorm_truncKernel (hΛ : 0 < Λ) (hs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (hd : 0 < d) : Integrable fun z => vecEuclideanNorm (truncKernel M z) := by
  set K := Λ ^ (d + 1) / ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal) with hK
  have hD : 0 < (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    mul_pos (by exact_mod_cast hd) (volume_euclideanBall_toReal_pos _ one_pos)
  have hK0 : 0 ≤ K := by positivity
  have hg : Integrable (Set.indicator (euclideanBall (0 : Vec d) 2)
      fun z => K * PDE.rieszKernelOne d z) := by
    rw [integrable_indicator_iff (measurableSet_euclideanBall _ _)]
    exact (PDE.integrableOn_euclideanBall_rieszKernelOne hd (by norm_num : (0 : ℝ) < 2)).const_mul K
  refine hg.mono' (measurable_vecEuclideanNorm.comp (measurable_truncKernel M)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
  by_cases hz : z ∈ euclideanBall (0 : Vec d) 2
  · rw [truncKernel, Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    by_cases h0 : z = 0
    · subst h0
      rw [newtonKernelMat_zero]
      have : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      rw [this]
      exact mul_nonneg hK0 (PDE.rieszKernelOne_nonneg _)
    · have := norm_newtonKernelMat_le hΛ hs hM hd h0
      have e : vecEuclideanNorm z ^ (1 - (d : ℤ)) = PDE.rieszKernelOne d z := by
        rw [PDE.rieszKernelOne, ← Real.rpow_intCast]; push_cast; rfl
      rwa [e] at this
  · rw [truncKernel, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    have : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
    simp [this]

/-- the truncated kernel `E_M 1_{B_2}` is integrable. -/
theorem integrable_truncKernel (hΛ : 0 < Λ) (hs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (hd : 0 < d) : Integrable (truncKernel M) :=
  (integrable_vecEuclideanNorm_truncKernel hΛ hs hM hd).mono'
    (measurable_truncKernel M).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => norm_le_vecEuclideanNorm _)

/-- representation `u^M_F(x) = ∫ Ẽ_M(x-y)·F(y) dy` for `x ∈ B_1`. -/
theorem newtonPotentialMat_eq_truncKernel {F : Vec d → Vec d}
    (hFs : tsupport F ⊆ euclideanBall (0 : Vec d) 1) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) 1) :
    PDE.newtonPotentialMat M F x = ∫ y, vecDot (truncKernel M (x - y)) (F y) := by
  unfold PDE.newtonPotentialMat
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : F y = 0
  · simp [hy, vecDot]
  · have hy1 : y ∈ euclideanBall (0 : Vec d) 1 := hFs (subset_tsupport _ hy)
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos, sub_zero] at hx hy1
    have : x - y ∈ euclideanBall (0 : Vec d) 2 := by
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt two_pos, sub_zero]
      have h := vecEuclideanNorm_add_le x (-y)
      rw [vecEuclideanNorm_neg, ← sub_eq_add_neg] at h
      linarith
    simp only [truncKernel, Set.indicator_of_mem this]

/-- Young's inequality `∫_{B_1} |u^M_F| ≤ K₁ ∫ |F|`, `K₁ = ‖Ẽ_M‖_{L¹}`. -/
theorem integral_abs_newtonPotentialMat_le (hΛ : 0 < Λ) (hs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (hd : 0 < d) {F : Vec d → Vec d} (hF : Continuous F)
    (hFs : tsupport F ⊆ euclideanBall (0 : Vec d) 1) :
    ∫ x in euclideanBall (0 : Vec d) 1, |PDE.newtonPotentialMat M F x| ≤
      truncKernelNorm M * ∫ x, vecEuclideanNorm (F x) := by
  set a : Vec d → ℝ := fun x => vecEuclideanNorm (F x) with ha_def
  set b : Vec d → ℝ := fun z => vecEuclideanNorm (truncKernel M z) with hb_def
  set L := ContinuousLinearMap.mul ℝ ℝ with hL
  have hFc : HasCompactSupport F :=
    (isCompact_euclideanClosedBall (0 : Vec d) zero_le_one).of_isClosed_subset (isClosed_tsupport _)
      (hFs.trans (euclideanBall_subset_euclideanClosedBall _ _))
  have hac : Continuous a := continuous_vecEuclideanNorm.comp hF
  have hacs : HasCompactSupport a :=
    hFc.comp_left (g := vecEuclideanNorm) (vecEuclideanNorm_eq_zero_iff.2 rfl)
  have ha : Integrable a := hac.integrable_of_hasCompactSupport hacs
  have hb : Integrable b := integrable_vecEuclideanNorm_truncKernel hΛ hs hM hd
  have hconv : Integrable (a ⋆[L] b) := ha.integrable_convolution L hb
  have hae := ha.ae_convolution_exists L hb
  have hpt : ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ euclideanBall (0 : Vec d) 1 →
      |PDE.newtonPotentialMat M F x| ≤ (a ⋆[L] b) x := by
    filter_upwards [hae] with x hx hxb
    rw [newtonPotentialMat_eq_truncKernel hFs hxb]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) hx
      (Filter.Eventually.of_forall fun y => ?_)
    have := abs_vecDot_le_vecEuclideanNorm_mul (truncKernel M (x - y)) (F y)
    simpa [hL, ha_def, hb_def, mul_comm] using this
  have h1 : ∫ x in euclideanBall (0 : Vec d) 1, |PDE.newtonPotentialMat M F x| ≤
      ∫ x in euclideanBall (0 : Vec d) 1, (a ⋆[L] b) x := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
      hconv.integrableOn ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_euclideanBall _ _)]
    filter_upwards [hpt] with x hx hxb using hx hxb
  have hnn : 0 ≤ᵐ[volume] (a ⋆[L] b) := by
    filter_upwards [hae] with x hx
    refine integral_nonneg fun y => ?_
    simp only [hL, ContinuousLinearMap.mul_apply']
    exact mul_nonneg (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_nonneg _)
  have h2 := setIntegral_le_integral hconv hnn (s := euclideanBall (0 : Vec d) 1)
  have h3 : ∫ x, (a ⋆[L] b) x = (∫ x, a x) * ∫ x, b x := by
    have := integral_convolution (L := L) ha hb
    simpa [hL] using this
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = truncKernelNorm M * ∫ x, vecEuclideanNorm (F x) := by
      rw [h3, mul_comm]; rfl

end

end AFree
