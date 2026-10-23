module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.EuclideanBall.Basic

/-!
# Euclidean smooth bumps on `Vec d`

Smooth cutoffs built from
`Real.smoothTransition` of a polynomial in `vecNormSq`, the standard mollifier, its rescalings,
and a smooth Urysohn function for compact subsets of the unit Euclidean ball.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

/-- The Euclidean cutoff `χ_{a,b}(x) = η₀((b'² - |x|²)/(b'² - a²))`, `b' = (a+b)/2`. -/
noncomputable def euclideanCutoff {d : ℕ} (a b : ℝ) : Vec d → ℝ :=
  fun x => Real.smoothTransition
    ((((a + b) / 2) ^ 2 - vecNormSq x) / (((a + b) / 2) ^ 2 - a ^ 2))

lemma contDiff_vecNormSq {d : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
  simp_rw [vecNormSq_eq_sum_sq]
  refine ContDiff.sum fun i _ => ?_
  exact (contDiff_apply ℝ ℝ i).pow 2

/-- Smoothness of the Euclidean cutoff. -/
theorem contDiff_euclideanCutoff {d : ℕ} (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanCutoff (d := d) a b) := by
  unfold euclideanCutoff
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_vecNormSq).div_const _)

/-- `0 ≤ χ_{a,b}`. -/
theorem euclideanCutoff_nonneg {d : ℕ} (a b : ℝ) (x : Vec d) :
    0 ≤ euclideanCutoff a b x := Real.smoothTransition.nonneg _

/-- `χ_{a,b} ≤ 1`. -/
theorem euclideanCutoff_le_one {d : ℕ} (a b : ℝ) (x : Vec d) :
    euclideanCutoff a b x ≤ 1 := Real.smoothTransition.le_one _

/-- `χ_{a,b} = 1` on the closed ball of radius `a`. -/
theorem euclideanCutoff_eq_one {d : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) {x : Vec d}
    (hx : vecEuclideanNorm x ≤ a) : euclideanCutoff a b x = 1 := by
  unfold euclideanCutoff
  apply Real.smoothTransition.one_of_one_le
  have hD : 0 < ((a + b) / 2) ^ 2 - a ^ 2 := by nlinarith
  rw [one_le_div hD]
  have h1 : vecNormSq x ≤ a ^ 2 := by
    have := vecEuclideanNorm_sq x
    nlinarith [vecEuclideanNorm_nonneg x]
  linarith

lemma euclideanCutoff_tsupport_subset {d : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    tsupport (euclideanCutoff (d := d) a b) ⊆ {x | vecNormSq x ≤ ((a + b) / 2) ^ 2} := by
  have hD : 0 < ((a + b) / 2) ^ 2 - a ^ 2 := by nlinarith
  apply closure_minimal
  · intro x hx
    simp only [Function.mem_support, euclideanCutoff, ne_eq,
      Real.smoothTransition.zero_iff_nonpos, not_le] at hx
    have := (div_pos_iff_of_pos_right hD).1 hx
    exact le_of_lt (by simpa using this)
  · exact isClosed_le (contDiff_vecNormSq.continuous) continuous_const

lemma isCompact_vecNormSq_le {d : ℕ} (r : ℝ) :
    IsCompact {x : Vec d | vecNormSq x ≤ r ^ 2} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (contDiff_vecNormSq.continuous) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Vec d)) (r := |r|)).subset ?_
    intro x hx
    rw [mem_closedBall_zero_iff]
    refine (norm_le_vecEuclideanNorm x).trans ?_
    have : vecEuclideanNorm x ^ 2 ≤ |r| ^ 2 := by
      rw [vecEuclideanNorm_sq, sq_abs]; exact hx
    exact le_of_sq_le_sq (by simpa using this) (abs_nonneg r) |> fun h => by
      simpa using h

/-- `tsupp χ_{a,b} ⊆ B_b`. -/
theorem tsupport_euclideanCutoff_subset {d : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    tsupport (euclideanCutoff (d := d) a b) ⊆ euclideanBall 0 b := by
  intro x hx
  have := euclideanCutoff_tsupport_subset ha hab hx
  simp only [Set.mem_ofPred_eq] at this
  show euclideanSqDist x 0 < b ^ 2
  simp only [euclideanSqDist, sub_zero]
  nlinarith

/-- `χ_{a,b}` has compact support. -/
theorem hasCompactSupport_euclideanCutoff {d : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    HasCompactSupport (euclideanCutoff (d := d) a b) :=
  (isCompact_vecNormSq_le ((a + b) / 2)).of_isClosed_subset (isClosed_tsupport _)
    (euclideanCutoff_tsupport_subset ha hab)

/-- A cutoff `χ`: `1` on `B_{1/2}`, support in `B_{3/4}`. -/
theorem euclideanCutoff_half_eq_one {d : ℕ} {x : Vec d} (hx : x ∈ euclideanBall 0 (1 / 2)) :
    euclideanCutoff (1 / 2) (3 / 4) x = 1 := by
  apply euclideanCutoff_eq_one (by norm_num) (by norm_num)
  have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
  simpa using this.le

/-- Support of the cutoff `χ`. -/
theorem tsupport_euclideanCutoff_half {d : ℕ} :
    tsupport (euclideanCutoff (d := d) (1 / 2) (3 / 4)) ⊆ euclideanBall 0 (3 / 4) :=
  tsupport_euclideanCutoff_subset (by norm_num) (by norm_num)

/-- The unnormalised mollifier profile. -/
noncomputable def stdMollifierProfile (d : ℕ) : Vec d → ℝ := euclideanCutoff (1 / 4) (1 / 2)

lemma stdMollifierProfile_integral_pos (d : ℕ) : 0 < ∫ x, stdMollifierProfile d x := by
  have hc : Continuous (stdMollifierProfile d) :=
    (contDiff_euclideanCutoff _ _).continuous
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_euclideanCutoff (by norm_num) (by norm_num))
    (euclideanCutoff_nonneg _ _) (x := 0) ?_
  rw [stdMollifierProfile, euclideanCutoff_eq_one (by norm_num) (by norm_num)]
  · exact one_ne_zero
  · have : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
    rw [this]; norm_num

/-- The standard mollifier `φ = χ_{1/4,1/2} / ∫ χ_{1/4,1/2}`. -/
noncomputable def stdMollifier (d : ℕ) : Vec d → ℝ :=
  fun x => stdMollifierProfile d x / ∫ y, stdMollifierProfile d y

/-- Smoothness of the standard mollifier. -/
theorem contDiff_stdMollifier (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (stdMollifier d) :=
  (contDiff_euclideanCutoff _ _).div_const _

/-- Nonnegativity of the standard mollifier. -/
theorem stdMollifier_nonneg (d : ℕ) (x : Vec d) : 0 ≤ stdMollifier d x :=
  div_nonneg (euclideanCutoff_nonneg _ _ _) (stdMollifierProfile_integral_pos d).le

/-- The standard mollifier has integral one (also for `d = 0`). -/
theorem integral_stdMollifier (d : ℕ) : ∫ x, stdMollifier d x = 1 := by
  unfold stdMollifier
  rw [integral_div]
  exact div_self (stdMollifierProfile_integral_pos d).ne'

lemma tsupport_stdMollifier_subset_profile (d : ℕ) :
    tsupport (stdMollifier d) ⊆ tsupport (euclideanCutoff (d := d) (1 / 4) (1 / 2)) := by
  apply closure_mono
  intro x hx
  simp only [Function.mem_support, stdMollifier, ne_eq, div_eq_zero_iff, not_or] at hx
  exact hx.1

/-- Support of the standard mollifier lies in `B_1`. -/
theorem tsupport_stdMollifier_subset (d : ℕ) : tsupport (stdMollifier d) ⊆ euclideanBall 0 1 :=
  (tsupport_stdMollifier_subset_profile d).trans
    ((tsupport_euclideanCutoff_subset (d := d) (by norm_num : (0:ℝ) < 1 / 4)
      (by norm_num)).trans (euclideanBall_mono (by norm_num) (by norm_num)))

/-- The standard mollifier has compact support. -/
theorem hasCompactSupport_stdMollifier (d : ℕ) : HasCompactSupport (stdMollifier d) :=
  (hasCompactSupport_euclideanCutoff (d := d) (by norm_num : (0:ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1 / 2)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_stdMollifier_subset_profile d)

/-- The rescaled mollifier `ε⁻ᵈ φ(z/ε)`. -/
noncomputable def scaledMollifier {d : ℕ} (ε : ℝ) : Vec d → ℝ :=
  fun z => (ε⁻¹) ^ d * stdMollifier d (ε⁻¹ • z)

/-- Smoothness of the scaled mollifier. -/
theorem contDiff_scaledMollifier {d : ℕ} (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledMollifier (d := d) ε) :=
  contDiff_const.mul ((contDiff_stdMollifier d).comp (contDiff_const_smul _))

/-- Nonnegativity of the scaled mollifier. -/
theorem scaledMollifier_nonneg {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (z : Vec d) :
    0 ≤ scaledMollifier ε z :=
  mul_nonneg (pow_nonneg (inv_nonneg.2 hε) _) (stdMollifier_nonneg d _)

/-- The scaled mollifier has integral one. -/
theorem integral_scaledMollifier {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∫ z, scaledMollifier (d := d) ε z = 1 := by
  unfold scaledMollifier
  rw [integral_const_mul,
    Measure.integral_comp_smul (volume : Measure (Vec d)) (stdMollifier d) ε⁻¹,
    integral_stdMollifier]
  simp only [Module.finrank_fin_fun, inv_pow, inv_inv, smul_eq_mul, mul_one]
  rw [abs_of_nonneg (pow_nonneg hε.le _)]
  exact inv_mul_cancel₀ (pow_pos hε _).ne'

lemma scaledMollifier_tsupport_subset_aux {d : ℕ} {ε : ℝ} :
    tsupport (scaledMollifier (d := d) ε) ⊆ (fun z => ε⁻¹ • z) ⁻¹' tsupport (stdMollifier d) := by
  have hcont : Continuous fun z : Vec d => ε⁻¹ • z := continuous_const_smul _
  have hsub : Function.support (scaledMollifier (d := d) ε) ⊆
      (fun z => ε⁻¹ • z) ⁻¹' tsupport (stdMollifier d) := by
    intro z hz
    simp only [Function.mem_support, scaledMollifier, ne_eq, mul_eq_zero, not_or] at hz
    exact subset_tsupport _ hz.2
  exact closure_minimal hsub ((isClosed_tsupport _).preimage hcont)

/-- Support of the scaled mollifier lies in `B_ε`. -/
theorem tsupport_scaledMollifier_subset {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tsupport (scaledMollifier (d := d) ε) ⊆ euclideanBall 0 ε := by
  intro z hz
  have h := tsupport_stdMollifier_subset d (scaledMollifier_tsupport_subset_aux hz)
  have h2 : vecNormSq (ε⁻¹ • z) < 1 ^ 2 := by simpa [euclideanBall, euclideanSqDist] using h
  show euclideanSqDist z 0 < ε ^ 2
  simp only [euclideanSqDist, sub_zero]
  rw [vecNormSq_smul] at h2
  have : ε ^ 2 * (ε⁻¹ ^ 2 * vecNormSq z) = vecNormSq z := by
    field_simp
  nlinarith [mul_lt_mul_of_pos_left h2 (pow_pos hε 2)]

/-- The scaled mollifier has compact support. -/
theorem hasCompactSupport_scaledMollifier {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (scaledMollifier (d := d) ε) := by
  have h : HasCompactSupport fun z : Vec d => stdMollifier d (ε⁻¹ • z) := by
    have := (hasCompactSupport_stdMollifier d).comp_isClosedEmbedding
      ((Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε.ne')).isClosedEmbedding)
    exact this
  exact h.mul_left

/-- Smooth Urysohn function for a compact `K ⊆ B_1`. -/
theorem exists_smooth_urysohn_euclideanBall {d : ℕ} {K : Set (Vec d)} (hK : IsCompact K)
    (hKB : K ⊆ euclideanBall 0 1) :
    ∃ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      (∀ x ∈ K, ψ x = 1) ∧ tsupport ψ ⊆ euclideanBall 0 1 ∧ HasCompactSupport ψ := by
  have hex : ∃ a : ℝ, 1 / 2 ≤ a ∧ a < 1 ∧ ∀ x ∈ K, vecEuclideanNorm x ≤ a := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1 / 2, le_rfl, by norm_num, by simp⟩
    · have hcont : ContinuousOn vecEuclideanNorm K := by
        unfold vecEuclideanNorm
        exact (Real.continuous_sqrt.comp contDiff_vecNormSq.continuous).continuousOn
      obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne hcont
      have hlt : vecEuclideanNorm x₀ < 1 :=
        by simpa using (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 (hKB hx₀)
      exact ⟨max (1 / 2) (vecEuclideanNorm x₀), le_max_left _ _, max_lt (by norm_num) hlt,
        fun x hx => (hmax hx).trans (le_max_right _ _)⟩
  obtain ⟨a, ha1, ha2, hKa⟩ := hex
  have ha0 : 0 < a := by linarith
  have hab : a < (1 + a) / 2 := by linarith
  refine ⟨euclideanCutoff a ((1 + a) / 2), contDiff_euclideanCutoff _ _,
    fun x => ⟨euclideanCutoff_nonneg _ _ _, euclideanCutoff_le_one _ _ _⟩,
    fun x hx => euclideanCutoff_eq_one ha0 hab (hKa x hx), ?_,
    hasCompactSupport_euclideanCutoff ha0 hab⟩
  exact (tsupport_euclideanCutoff_subset ha0 hab).trans
    (euclideanBall_mono (by linarith) (by linarith))

end AFree
