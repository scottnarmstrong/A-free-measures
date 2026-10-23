module

public import AFree.Harmonic.WeakTypeKernel.Basic

/-!
# The Hörmander estimate for a scalar kernel with a gradient bound

A smooth kernel with `|∇K v| ≤ A |v| / |x|^{d+1}` satisfies the Hölder-type bound
`|K z - K z'| ≤ 2^{d+1} A |z - z'| / |z|^{d+1}` for `|z - z'| ≤ |z|/2`, and consequently, for a
mean-zero `b` supported in `B(c, r)`, `∫_{B(c, 2r)ᶜ} |∫ K(x - y) b(y) dy| dx ≤ C(d) A ‖b‖₁`.
-/

@[expose] public section

open MeasureTheory Set Filter PDE PDE.NewtonWeakType
open scoped ENNReal Topology

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The Hörmander gradient condition implies the Hölder-type bound on `K`. -/
theorem abs_kernel_sub_le {K : Vec d → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K) {A : ℝ} (hA : 0 ≤ A)
    (hgrad : ∀ x : Vec d, x ≠ 0 → ∀ v : Vec d,
      |fderiv ℝ K x v| ≤ A * vecEuclideanNorm v / vecEuclideanNorm x ^ (d + 1))
    {z w : Vec d} (hz : z ≠ 0) (hw : vecEuclideanNorm w ≤ vecEuclideanNorm z / 2) :
    |K z - K (z - w)| ≤ 2 ^ (d + 1) * A * vecEuclideanNorm w / vecEuclideanNorm z ^ (d + 1) := by
  have hzpos : 0 < vecEuclideanNorm z := vecEuclideanNorm_pos_iff.mpr hz
  have hdiff : Differentiable ℝ K := hK.differentiable (by simp)
  set φ : ℝ → ℝ := fun t => K (z - t • w) with hφ
  set C : ℝ := 2 ^ (d + 1) * A * vecEuclideanNorm w / vecEuclideanNorm z ^ (d + 1) with hC
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, vecEuclideanNorm z / 2 ≤ vecEuclideanNorm (z - t • w) := by
    intro t ht
    have h1 := vecEuclideanNorm_add_le (z - t • w) (t • w)
    rw [sub_add_cancel, vecEuclideanNorm_smul, abs_of_nonneg ht.1] at h1
    have : t * vecEuclideanNorm w ≤ vecEuclideanNorm w :=
      mul_le_of_le_one_left (vecEuclideanNorm_nonneg _) ht.2
    linarith
  have hder : ∀ t : ℝ, HasDerivAt φ (-(fderiv ℝ K (z - t • w) w)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => z - t • w) (-w) t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_sub z
    have h2 := (hdiff (z - t • w)).hasFDerivAt.comp_hasDerivAt t h1
    rw [map_neg] at h2
    exact h2
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖-(fderiv ℝ K (z - t • w) w)‖ ≤ C := by
    intro t ht
    have hp := hpt t ⟨ht.1, ht.2.le⟩
    have hp0 : 0 < vecEuclideanNorm (z - t • w) := by linarith
    have hne : z - t • w ≠ 0 := vecEuclideanNorm_pos_iff.mp hp0
    rw [norm_neg, Real.norm_eq_abs]
    refine (hgrad _ hne w).trans ?_
    have hpow : (vecEuclideanNorm z / 2) ^ (d + 1) ≤ vecEuclideanNorm (z - t • w) ^ (d + 1) :=
      pow_le_pow_left₀ (by positivity) hp _
    have hnum : 0 ≤ A * vecEuclideanNorm w := mul_nonneg hA (vecEuclideanNorm_nonneg _)
    calc A * vecEuclideanNorm w / vecEuclideanNorm (z - t • w) ^ (d + 1)
        ≤ A * vecEuclideanNorm w / (vecEuclideanNorm z / 2) ^ (d + 1) :=
          div_le_div_of_nonneg_left hnum (by positivity) hpow
      _ = C := by rw [hC, div_pow]; field_simp
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ)
    (f' := fun t => -(fderiv ℝ K (z - t • w) w)) (a := 0) (b := 1) (C := C)
    (fun t _ => (hder t).hasDerivWithinAt) hbound 1 ⟨zero_le_one, le_rfl⟩
  have e1 : φ 1 = K (z - w) := by simp [hφ]
  have e0 : φ 0 = K z := by simp [hφ]
  rw [e1, e0, Real.norm_eq_abs, abs_sub_comm] at hmv
  simpa using hmv

/-- Pointwise Hörmander bound for a scalar kernel, for `|x - c| ≥ 2r` and `b` supported in
`|y - c| ≤ r`. -/
theorem abs_integral_kernel_sub_le [NeZero d] {K : Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ z z' : Vec d, z ≠ 0 → vecEuclideanNorm (z - z') ≤ vecEuclideanNorm z / 2 →
      |K z - K z'| ≤ B * vecEuclideanNorm (z - z') / vecEuclideanNorm z ^ (d + 1))
    (hKm : ∀ x : Vec d, AEStronglyMeasurable (fun y => K (x - y)) volume)
    {c : Vec d} {r : ℝ} (hr : 0 < r) {b : Vec d → ℝ} (hb : Integrable b)
    (hsupp : ∀ y, r < vecEuclideanNorm (y - c) → b y = 0) {x : Vec d}
    (hx : 2 * r ≤ vecEuclideanNorm (x - c)) :
    |∫ y, (K (x - y) - K (x - c)) * b y| ≤
      B * r / vecEuclideanNorm (x - c) ^ (d + 1) * ∫ y, |b y| := by
  set z := x - c with hz
  have hzpos : 0 < vecEuclideanNorm z := by linarith
  have hz0 : z ≠ 0 := fun h => by simp [h, vecEuclideanNorm_eq_zero_iff.mpr rfl] at hzpos
  have hpow : 0 < vecEuclideanNorm z ^ (d + 1) := pow_pos hzpos _
  let G : Vec d → ℝ := fun y => B * (r / vecEuclideanNorm z ^ (d + 1)) * |b y|
  have hG : Integrable G := hb.abs.const_mul _
  have hfG : ∀ y, |(K (x - y) - K (x - c)) * b y| ≤ G y := by
    intro y
    by_cases hy : vecEuclideanNorm (y - c) ≤ r
    · have hsub : z - (x - y) = y - c := by simp [hz]
      have hhalf : vecEuclideanNorm (z - (x - y)) ≤ vecEuclideanNorm z / 2 := by
        rw [hsub]; linarith
      have h1 := hK z (x - y) hz0 hhalf
      rw [hsub] at h1
      rw [abs_mul, abs_sub_comm]
      have h2 : B * vecEuclideanNorm (y - c) / vecEuclideanNorm z ^ (d + 1) ≤
          B * (r / vecEuclideanNorm z ^ (d + 1)) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy hB) hpow.le
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (abs_nonneg _)
    · rw [hsupp y (not_le.mp hy)]
      simp only [mul_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hB (div_nonneg hr.le hpow.le)) (abs_nonneg _)
  have hmeas : AEStronglyMeasurable (fun y => (K (x - y) - K (x - c)) * b y) volume :=
    ((hKm x).sub aestronglyMeasurable_const).mul hb.aestronglyMeasurable
  have hint : Integrable (fun y => (K (x - y) - K (x - c)) * b y) :=
    hG.mono' hmeas (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hfG y)
  calc |∫ y, (K (x - y) - K (x - c)) * b y| ≤ ∫ y, |(K (x - y) - K (x - c)) * b y| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, G y := integral_mono hint.abs hG hfG
    _ = B * r / vecEuclideanNorm z ^ (d + 1) * ∫ y, |b y| := by
      simp only [G]
      rw [integral_const_mul]
      ring

/-- **Hörmander integral.** For `b` supported in `|y - c| ≤ r`, the exterior integral over
`B(c, 2r)ᶜ` of the Hörmander integrand is bounded by `C(d) B ‖b‖₁`. -/
theorem lintegral_exterior_kernel_sub_le [NeZero d] {K : Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ z z' : Vec d, z ≠ 0 → vecEuclideanNorm (z - z') ≤ vecEuclideanNorm z / 2 →
      |K z - K z'| ≤ B * vecEuclideanNorm (z - z') / vecEuclideanNorm z ^ (d + 1))
    (hKm : ∀ x : Vec d, AEStronglyMeasurable (fun y => K (x - y)) volume)
    {c : Vec d} {r : ℝ} (hr : 0 < r) {b : Vec d → ℝ} (hb : Integrable b)
    (hsupp : ∀ y, r < vecEuclideanNorm (y - c) → b y = 0) :
    ∫⁻ x in (euclideanBall c (2 * r))ᶜ,
        ENNReal.ofReal |∫ y, (K (x - y) - K (x - c)) * b y| ≤
      ENNReal.ofReal (hormanderConst d * B * ∫ y, |b y|) := by
  set M : ℝ := ∫ y, |b y| with hM
  have hM0 : 0 ≤ M := integral_nonneg fun y => abs_nonneg _
  have hr2 : 0 < 2 * r := by linarith
  have hpt : ∀ x ∈ (euclideanBall c (2 * r))ᶜ,
      ENNReal.ofReal |∫ y, (K (x - y) - K (x - c)) * b y| ≤
        ENNReal.ofReal (B * r * M) *
          ENNReal.ofReal (vecEuclideanNorm (x - c) ^ (-((d : ℝ) + 1))) := by
    intro x hx
    have hx' : 2 * r ≤ vecEuclideanNorm (x - c) := by
      have : ¬ vecEuclideanNorm (x - c) < 2 * r := fun h =>
        hx ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr2).mpr h)
      exact not_lt.mp this
    have hbd := abs_integral_kernel_sub_le hB hK hKm hr hb hsupp hx'
    have hzpos : 0 < vecEuclideanNorm (x - c) := by linarith
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    refine hbd.trans (le_of_eq ?_)
    rw [Real.rpow_neg hzpos.le, ← Real.rpow_natCast, Nat.cast_add, Nat.cast_one]
    field_simp
    rw [hM]
  calc
    _ ≤ ∫⁻ x in (euclideanBall c (2 * r))ᶜ, ENNReal.ofReal (B * r * M) *
          ENNReal.ofReal (vecEuclideanNorm (x - c) ^ (-((d : ℝ) + 1))) :=
      setLIntegral_mono' (measurableSet_euclideanBall c _).compl hpt
    _ = ENNReal.ofReal (B * r * M) * ∫⁻ x in (euclideanBall c (2 * r))ᶜ,
          ENNReal.ofReal (vecEuclideanNorm (x - c) ^ (-((d : ℝ) + 1))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (B * r * M) * ENNReal.ofReal
          ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * (2 * r)⁻¹) := by
      rw [lintegral_compl_euclideanBall_comp_sub c (2 * r)
        (fun t => ENNReal.ofReal (t ^ (-((d : ℝ) + 1)))),
        lintegral_compl_euclideanBall_tail hr2]
    _ = ENNReal.ofReal (hormanderConst d * B * M) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold hormanderConst
      field_simp

/-- For mean-zero `b`, the exterior integral of `|∫ K(x - y) b(y) dy|` is bounded by the
Hörmander integral, with constant `C(d) A`. -/
theorem lintegral_exterior_kernel_le [NeZero d] {K : Vec d → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hKi : Integrable K) {A : ℝ} (hA : 0 ≤ A)
    (hgrad : ∀ x : Vec d, x ≠ 0 → ∀ v : Vec d,
      |fderiv ℝ K x v| ≤ A * vecEuclideanNorm v / vecEuclideanNorm x ^ (d + 1))
    {c : Vec d} {r : ℝ} (hr : 0 < r) {b : Vec d → ℝ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (hsupp : ∀ y, r < vecEuclideanNorm (y - c) → b y = 0)
    (hmean : ∫ y, b y = 0) :
    ∫⁻ x in (euclideanBall c (2 * r))ᶜ, ENNReal.ofReal |∫ y, K (x - y) * b y| ≤
      ENNReal.ofReal (hormanderConst d * (2 ^ (d + 1) * A) * ∫ y, |b y|) := by
  have hbi : Integrable b := hb.integrable_of_hasCompactSupport hbc
  have hB : 0 ≤ 2 ^ (d + 1) * A := by positivity
  have hHol : ∀ z z' : Vec d, z ≠ 0 → vecEuclideanNorm (z - z') ≤ vecEuclideanNorm z / 2 →
      |K z - K z'| ≤ 2 ^ (d + 1) * A * vecEuclideanNorm (z - z') / vecEuclideanNorm z ^ (d + 1) := by
    intro z z' hz hzz
    have := abs_kernel_sub_le hK hA hgrad hz (w := z - z') hzz
    simpa using this
  have hKm : ∀ x : Vec d, AEStronglyMeasurable (fun y => K (x - y)) volume := fun x =>
    (hK.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  refine le_trans (le_of_eq ?_) (lintegral_exterior_kernel_sub_le hB hHol hKm hr hbi hsupp)
  refine setLIntegral_congr_fun (measurableSet_euclideanBall c _).compl fun x _ => ?_
  congr 2
  have hint := integrable_kernel_mul hKi hb hbc x
  have hsplit : ∀ y, (K (x - y) - K (x - c)) * b y = K (x - y) * b y - K (x - c) * b y := fun y => by
    ring
  simp_rw [hsplit]
  rw [integral_sub hint (hbi.const_mul _), integral_const_mul, hmean]
  simp

end

end AFree
