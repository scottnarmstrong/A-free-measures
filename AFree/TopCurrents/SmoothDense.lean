module

public import AFree.TopCurrents.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Smooth density in `L¹`
-/

@[expose] public section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace AFree

open PDE

/-- For `g ∈ L¹(𝓛^d)` and `η > 0` there is `φ ∈ C_c^∞(ℝ^d)` with `∫ |g - φ| < η`. -/
theorem smoothdense {d : ℕ} {g : Vec d → ℝ} (hg : Integrable g volume) {η : ℝ} (hη : 0 < η) :
    ∃ φ : Vec d → ℝ, IsTestFunctionOn Set.univ φ ∧ ∫ x, |g x - φ x| < η := by
  obtain ⟨χ, hχc, hχint, hχcont, hχi⟩ := hg.exists_hasCompactSupport_integral_sub_le (half_pos hη)
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.subset_closedBall (0 : Vec d)
  set R1 : ℝ := max R 0 + 1 with hR1
  have hR1pos : 0 < R1 := by positivity
  set θ : ContDiffBump (0 : Vec d) := ⟨R1, R1 + 1, hR1pos, by linarith⟩ with hθ
  set Vol : ℝ := (volume (closedBall (0 : Vec d) (R1 + 1))).toReal with hVol
  have hV0 : 0 ≤ Vol := ENNReal.toReal_nonneg
  set δ : ℝ := η / (4 * (Vol + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hunif : UniformContinuous χ := hχc.uniformContinuous_of_continuous hχcont
  obtain ⟨ψ, hψ, hψd⟩ := hunif.exists_contDiff_dist_le hδpos
  set φ : Vec d → ℝ := fun x => θ x * ψ x with hφ
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := θ.contDiff.mul hψ
  have hφc : HasCompactSupport φ := θ.hasCompactSupport.mul_right
  have hφcont : Continuous φ := hφs.continuous
  have hbound : ∀ x, |χ x - φ x| ≤ (closedBall (0 : Vec d) (R1 + 1)).indicator (fun _ => δ) x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : Vec d) (R1 + 1)
    · rw [Set.indicator_of_mem hx]
      by_cases hx1 : x ∈ closedBall (0 : Vec d) R1
      · have h1 : θ x = 1 := θ.one_of_mem_closedBall hx1
        simp only [hφ, h1, one_mul]
        have := hψd x
        rw [Real.dist_eq] at this
        rw [abs_sub_comm]; exact this.le
      · have hχx : χ x = 0 := by
          by_contra h
          exact hx1 ((hR.trans (closedBall_subset_closedBall (by linarith [le_max_left R 0]))) (subset_tsupport _ h))
        have h2 : θ x ≤ 1 := θ.le_one
        have h3 : 0 ≤ θ x := θ.nonneg
        have := hψd x
        rw [Real.dist_eq, hχx] at this
        simp only [hφ, hχx, zero_sub, abs_neg, abs_mul, abs_of_nonneg h3]
        calc θ x * |ψ x| ≤ 1 * |ψ x| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
          _ ≤ δ := by rw [one_mul]; simpa using this.le
    · rw [Set.indicator_of_notMem hx]
      have h0 : θ x = 0 := θ.zero_of_le_dist (by
        rw [mem_closedBall, not_le] at hx; simpa using hx.le)
      have hχx : χ x = 0 := by
        by_contra h
        have := (hR.trans (closedBall_subset_closedBall (by linarith [le_max_left R 0] : R ≤ R1 + 1)))
          (subset_tsupport _ h)
        exact hx this
      simp [hφ, h0, hχx]
  refine ⟨φ, ⟨hφs, hφc, Set.subset_univ _⟩, ?_⟩
  have hφi : Integrable φ volume := hφcont.integrable_of_hasCompactSupport hφc
  have hint2 : Integrable (fun x => |g x - φ x|) volume := (hg.sub hφi).abs
  have h1 : Integrable (fun x => ‖g x - χ x‖) volume := (hg.sub hχi).norm
  have h2 : Integrable (fun x => |χ x - φ x|) volume := (hχi.sub hφi).abs
  have hstep : ∫ x, |g x - φ x| ≤ (∫ x, ‖g x - χ x‖) + ∫ x, |χ x - φ x| := by
    rw [← integral_add h1 h2]
    refine integral_mono hint2 (h1.add h2) fun x => ?_
    simp only [Real.norm_eq_abs]
    calc |g x - φ x| = |(g x - χ x) + (χ x - φ x)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hindInt : Integrable ((closedBall (0 : Vec d) (R1 + 1)).indicator (fun _ => δ)) volume :=
    (integrableOn_const (measure_closedBall_lt_top (x := (0 : Vec d)) (r := R1 + 1)).ne).integrable_indicator
      measurableSet_closedBall
  have hind : ∫ x, |χ x - φ x| ≤ δ * Vol := by
    calc ∫ x, |χ x - φ x| ≤ ∫ x, (closedBall (0 : Vec d) (R1 + 1)).indicator (fun _ => δ) x :=
          integral_mono (hχi.sub hφi).abs hindInt hbound
      _ = δ * Vol := by
          rw [integral_indicator_const _ measurableSet_closedBall]
          simp [Measure.real, hVol, mul_comm]
  have hδV : δ * Vol ≤ η / 4 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hη.le hV0]
  linarith

end AFree
