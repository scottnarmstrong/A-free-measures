module

public import AFree.Rademacher.X0
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The cut-off function of AM Lemma 4.11

The product cut-off `φ(x) = ∏ᵢ χ(xᵢ - x̄ᵢ)` the cut-off `φ` of the proof of [AM, Lemma 4.11].
-/

@[expose] public section

open PDE Filter Topology Set

namespace AFree.Rademacher

variable {d : ℕ}

/-- The derivative of `Real.smoothTransition` is bounded (it vanishes off `[0, 1]`). -/
theorem exists_deriv_smoothTransition_bound : ∃ c₀ : ℝ, 0 ≤ c₀ ∧
    ∀ s, |deriv Real.smoothTransition s| ≤ c₀ := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨c, hc⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max c 0, le_max_right _ _, fun s => ?_⟩
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · exact (hc s hs).trans (le_max_left _ _)
  · simp only [mem_Icc, not_and_or, not_le] at hs
    have : deriv Real.smoothTransition s = 0 := by
      rcases hs with hs | hs
      · have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => 0 :=
          Filter.mem_of_superset (Iio_mem_nhds hs) fun y hy =>
            Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
        rw [this.deriv_eq]; simp
      · have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => 1 :=
          Filter.mem_of_superset (Ioi_mem_nhds hs) fun y hy =>
            Real.smoothTransition.one_of_one_le (le_of_lt hy)
        rw [this.deriv_eq]; simp
    rw [this]; simp

/-- The one-dimensional factor `χ(t) = T((b² - t²) / (b² - a²))`. -/
noncomputable def cutFactor (a b t : ℝ) : ℝ := Real.smoothTransition ((b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2))

theorem contDiff_cutFactor (a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutFactor a b) := by
  unfold cutFactor
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_id.pow 2)).div_const _)

theorem cutFactor_eq_one {a b t : ℝ} (hab : a < b) (ha : 0 < a) (ht : |t| ≤ a) :
    cutFactor a b t = 1 := by
  unfold cutFactor
  apply Real.smoothTransition.one_of_one_le
  have hD : 0 < b ^ 2 - a ^ 2 := by nlinarith
  rw [one_le_div hD]
  have : t ^ 2 ≤ a ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  linarith

theorem cutFactor_eq_zero {a b t : ℝ} (hab : a < b) (ha : 0 < a) (ht : b ≤ |t|) :
    cutFactor a b t = 0 := by
  unfold cutFactor
  apply Real.smoothTransition.zero_of_nonpos
  have hD : 0 < b ^ 2 - a ^ 2 := by nlinarith
  rw [div_nonpos_iff]; right
  refine ⟨?_, hD.le⟩
  have hb0 : 0 ≤ b := by linarith
  have : b ^ 2 ≤ t ^ 2 := by rw [← sq_abs t]; exact pow_le_pow_left₀ hb0 ht 2
  linarith

theorem abs_deriv_cutFactor_le {a b c₀ : ℝ} (hab : a < b) (ha : 0 < a) (hc₀ : 0 ≤ c₀)
    (hc : ∀ s, |deriv Real.smoothTransition s| ≤ c₀) (t : ℝ) :
    |deriv (cutFactor a b) t| ≤ 2 * c₀ / (b - a) := by
  have hD : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hba : 0 < b - a := by linarith
  have hder : HasDerivAt (cutFactor a b)
      (deriv Real.smoothTransition ((b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2)) *
        (-(2 * t) / (b ^ 2 - a ^ 2))) t := by
    have h1 : HasDerivAt (fun t : ℝ => (b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2))
        (-(2 * t) / (b ^ 2 - a ^ 2)) t := by
      have := ((hasDerivAt_pow 2 t).const_sub (b ^ 2)).div_const (b ^ 2 - a ^ 2)
      simpa using this
    exact ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt.comp t h1
  rw [hder.deriv]
  by_cases ht : |t| ≤ b
  · rw [abs_mul, abs_div, abs_neg, abs_mul, abs_of_pos hD, abs_two]
    have h1 := hc ((b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2))
    have h2 : 2 * |t| / (b ^ 2 - a ^ 2) ≤ 2 / (b - a) := by
      rw [div_le_div_iff₀ hD hba]
      have : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
      rw [this]
      nlinarith [abs_nonneg t]
    calc |deriv Real.smoothTransition ((b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2))| *
          (2 * |t| / (b ^ 2 - a ^ 2)) ≤ c₀ * (2 / (b - a)) :=
          mul_le_mul h1 h2 (by positivity) hc₀
      _ = 2 * c₀ / (b - a) := by ring
  · have hs : (b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2) < 0 := by
      have : b ^ 2 < t ^ 2 := by
        have hb0 : 0 ≤ b := by linarith
        rw [← sq_abs t]; exact pow_lt_pow_left₀ (not_le.1 ht) hb0 two_ne_zero
      exact div_neg_of_neg_of_pos (by linarith) hD
    have : deriv Real.smoothTransition ((b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2)) = 0 := by
      have : Real.smoothTransition =ᶠ[𝓝 ((b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2))] fun _ => 0 :=
        Filter.mem_of_superset (Iio_mem_nhds hs) fun y hy =>
          Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [this.deriv_eq]; simp
    rw [this]; simp only [zero_mul, abs_zero]; positivity

/-- The product cut-off `φ(x) = ∏ᵢ χ(xᵢ - x̄ᵢ)`. -/
noncomputable def cutProd (a b : ℝ) (xb x : Vec d) : ℝ := ∏ i, cutFactor a b (x i - xb i)

theorem contDiff_cutProd (a b : ℝ) (xb : Vec d) : ContDiff ℝ (⊤ : ℕ∞) (cutProd a b xb) := by
  unfold cutProd
  refine contDiff_prod fun i _ => ?_
  exact (contDiff_cutFactor a b).comp ((contDiff_apply ℝ ℝ i).sub contDiff_const)

theorem euclGrad_cutProd_apply {a b : ℝ} (xb x : Vec d) (i : Fin d) :
    euclGrad (cutProd a b xb) x i =
      deriv (cutFactor a b) (x i - xb i) *
        ∏ j ∈ Finset.univ.erase i, cutFactor a b (x j - xb j) := by
  have hφ : Differentiable ℝ (cutProd a b xb) := (contDiff_cutProd a b xb).differentiable (by simp)
  have h1 : HasDerivAt (fun t : ℝ => x + t • basisVec i) (basisVec i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec i)).const_add x
  have h2 : HasDerivAt (fun t : ℝ => cutProd a b xb (x + t • basisVec i))
      (fderiv ℝ (cutProd a b xb) x (basisVec i)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (l := cutProd a b xb) 0 (by simpa using (hφ x).hasFDerivAt) h1
      (by simp)
  have hfun : (fun t : ℝ => cutProd a b xb (x + t • basisVec i)) =
      fun t => cutFactor a b (x i - xb i + t) *
        ∏ j ∈ Finset.univ.erase i, cutFactor a b (x j - xb j) := by
    funext t
    unfold cutProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [basisVec]; ring_nf
    · refine Finset.prod_congr rfl fun j hj => ?_
      have : j ≠ i := Finset.ne_of_mem_erase hj
      simp [basisVec, this]
  have h3 : HasDerivAt (fun t : ℝ => cutFactor a b (x i - xb i + t))
      (deriv (cutFactor a b) (x i - xb i)) 0 := by
    have hd : DifferentiableAt ℝ (cutFactor a b) (x i - xb i + 0) :=
      ((contDiff_cutFactor a b).differentiable (by simp)) _
    have := hd.hasDerivAt.comp_const_add (x i - xb i) 0
    simpa using this
  have h4 := h3.mul_const (∏ j ∈ Finset.univ.erase i, cutFactor a b (x j - xb j))
  rw [← hfun] at h4
  exact h2.unique h4

/-- The cut-off `φ`. There is a constant `c₁ ≥ 0` depending only
on `d` such that for `0 < r < r'`, `κ = (r' - r)/3` and every `x̄ ∈ ℝ^d` there is a smooth
`φ : ℝ^d → ℝ` with `0 ≤ φ ≤ 1`, `φ = 1` on the neighbourhood `{‖x - x̄‖_∞ < r + κ}` of the closed
ball `B̄(x̄, r)`, `supp φ ⊆ B̄(x̄, r + 2κ) ⊆ B̄(x̄, r')` (max-norm balls), and
`|∇φ| ≤ c₁ / (r' - r)` for the Euclidean norm of the gradient. -/
theorem cutoff_function (d : ℕ) : ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ (xb : Vec d) (r r' : ℝ), 0 < r → r < r' →
    ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x, ‖x - xb‖ < r + (r' - r) / 3 → φ x = 1) ∧
      tsupport φ ⊆ Metric.closedBall xb (r + 2 * ((r' - r) / 3)) ∧
      tsupport φ ⊆ Metric.closedBall xb r' ∧
      ∀ x, vecEuclideanNorm (euclGrad φ x) ≤ c₁ / (r' - r) := by
  obtain ⟨c₀, hc₀, hc⟩ := exists_deriv_smoothTransition_bound
  refine ⟨6 * Real.sqrt d * c₀, by positivity, fun xb r r' hr hrr' => ?_⟩
  set κ := (r' - r) / 3 with hκ
  have hκpos : 0 < κ := by rw [hκ]; linarith
  set a := r + κ with ha
  set b := r + 2 * κ with hb
  have hab : a < b := by rw [ha, hb]; linarith
  have hapos : 0 < a := by rw [ha]; linarith
  have hbr' : b < r' := by rw [hb, hκ]; linarith
  refine ⟨cutProd a b xb, contDiff_cutProd a b xb, fun x => ?_, fun x hx => ?_, ?_, ?_, fun x => ?_⟩
  · unfold cutProd
    exact ⟨Finset.prod_nonneg fun i _ => Real.smoothTransition.nonneg _,
      Finset.prod_le_one₀ (fun i _ => Real.smoothTransition.nonneg _)
        fun i _ => Real.smoothTransition.le_one _⟩
  · unfold cutProd
    refine Finset.prod_eq_one fun i _ => cutFactor_eq_one hab hapos ?_
    have := norm_le_pi_norm (x - xb) i
    rw [Real.norm_eq_abs] at this
    simp only [Pi.sub_apply] at this
    exact this.trans hx.le
  · have hsupp : Function.support (cutProd a b xb) ⊆ Metric.closedBall xb b := by
      intro x hx
      rw [mem_closedBall_iff_norm]
      have hall : ∀ i, |x i - xb i| < b := by
        intro i
        by_contra hcon
        apply hx
        unfold cutProd
        exact Finset.prod_eq_zero (Finset.mem_univ i)
          (cutFactor_eq_zero hab hapos (not_lt.1 hcon))
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
      simp only [Pi.sub_apply, Real.norm_eq_abs]; exact (hall i).le
    exact closure_minimal hsupp Metric.isClosed_closedBall
  · have hsupp : Function.support (cutProd a b xb) ⊆ Metric.closedBall xb r' := by
      intro x hx
      rw [mem_closedBall_iff_norm]
      have hall : ∀ i, |x i - xb i| < b := by
        intro i
        by_contra hcon
        apply hx
        unfold cutProd
        exact Finset.prod_eq_zero (Finset.mem_univ i)
          (cutFactor_eq_zero hab hapos (not_lt.1 hcon))
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
      simp only [Pi.sub_apply, Real.norm_eq_abs]; linarith [hall i]
    exact closure_minimal hsupp Metric.isClosed_closedBall
  · have hcomp : ∀ i, |euclGrad (cutProd a b xb) x i| ≤ 2 * c₀ / (b - a) := by
      intro i
      rw [euclGrad_cutProd_apply, abs_mul]
      have h1 := abs_deriv_cutFactor_le hab hapos hc₀ hc (x i - xb i)
      have h2 : |∏ j ∈ Finset.univ.erase i, cutFactor a b (x j - xb j)| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => by
          unfold cutFactor
          rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
          exact Real.smoothTransition.le_one _
      calc _ ≤ 2 * c₀ / (b - a) * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by have : 0 < b - a := by linarith
                                                positivity)
        _ = _ := mul_one _
    have hnorm : ‖euclGrad (cutProd a b xb) x‖ ≤ 2 * c₀ / (b - a) := by
      refine (pi_norm_le_iff_of_nonneg (by have : 0 < b - a := by linarith
                                           positivity)).2 fun i => ?_
      rw [Real.norm_eq_abs]; exact hcomp i
    refine (vecEuclideanNorm_le_sqrt_natCast_mul_norm _).trans ?_
    have hba : b - a = (r' - r) / 3 := by rw [ha, hb, hκ]; ring
    rw [hba] at hnorm
    calc Real.sqrt d * ‖euclGrad (cutProd a b xb) x‖
        ≤ Real.sqrt d * (2 * c₀ / ((r' - r) / 3)) :=
          mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
      _ = 6 * Real.sqrt d * c₀ / (r' - r) := by
          have : r' - r ≠ 0 := by linarith
          field_simp; ring

end AFree.Rademacher
