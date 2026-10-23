module

public import AFree.MetricCurrents.AKChain1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The auxiliary function for alternation

A `C¹` function `φ` with `φ(n) = n`, `φ' ≥ 0` bounded, `|φ(t) - t| ≤ 1/2` and
`φ'(s) φ'(s + 1/2) = 0`. We take `φ(t) = ∫₀ᵗ π max(0, cos 2πs) ds` (the derivative is supported
in the windows `[n - 1/4, n + 1/4]`).
-/

@[expose] public section

open MeasureTheory Filter Topology intervalIntegral Real

namespace AFree.AKAltAux

/-- The derivative `φ'(s) = π max(0, cos 2πs)`. -/
noncomputable def phiDer (s : ℝ) : ℝ := π * max 0 (cos (2 * π * s))

lemma phiDer_continuous : Continuous phiDer := by
  unfold phiDer; fun_prop

lemma phiDer_nonneg (s : ℝ) : 0 ≤ phiDer s := by
  unfold phiDer; exact mul_nonneg pi_pos.le (le_max_left _ _)

lemma phiDer_le (s : ℝ) : phiDer s ≤ π := by
  unfold phiDer
  refine mul_le_of_le_one_right pi_pos.le (max_le zero_le_one (cos_le_one _))

lemma phiDer_periodic : Function.Periodic phiDer 1 := fun s => by
  unfold phiDer
  rw [show 2 * π * (s + 1) = 2 * π * s + 2 * π by ring, cos_add_two_pi]

lemma phiDer_mul (s : ℝ) : phiDer s * phiDer (s + 1 / 2) = 0 := by
  unfold phiDer
  rw [show 2 * π * (s + 1 / 2) = 2 * π * s + π by ring, cos_add_pi]
  rcases le_total 0 (cos (2 * π * s)) with h | h
  · rw [max_eq_left (by linarith : -cos (2 * π * s) ≤ 0)]; ring
  · rw [max_eq_left h]; ring

/-- `φ(t) = ∫₀ᵗ φ'`. -/
noncomputable def phi (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, phiDer s

lemma hasDerivAt_phi (t : ℝ) : HasDerivAt phi (phiDer t) t :=
  integral_hasDerivAt_right (phiDer_continuous.intervalIntegrable _ _)
    (phiDer_continuous.stronglyMeasurableAtFilter _ _) phiDer_continuous.continuousAt

lemma deriv_phi : deriv phi = phiDer := funext fun t => (hasDerivAt_phi t).deriv

lemma integral_pos_piece {a b : ℝ} (h : ∀ s ∈ Set.uIcc a b, 0 ≤ cos (2 * π * s)) :
    ∫ s in a..b, phiDer s = (sin (2 * π * b) - sin (2 * π * a)) / 2 := by
  have e : ∫ s in a..b, phiDer s = ∫ s in a..b, π * cos (2 * π * s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [phiDer, max_eq_right (h s hs)]
  rw [e]
  have hd : ∀ s ∈ Set.uIcc a b, HasDerivAt (fun s => sin (2 * π * s) / 2) (π * cos (2 * π * s)) s := by
    intro s _
    have := ((hasDerivAt_id s).const_mul (2 * π)).sin.div_const 2
    refine this.congr_deriv ?_
    simp only [id, mul_one]; ring
  rw [integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => π * cos (2 * π * s)).intervalIntegrable _ _)]
  ring

lemma integral_zero_piece {a b : ℝ} (h : ∀ s ∈ Set.uIcc a b, cos (2 * π * s) ≤ 0) :
    ∫ s in a..b, phiDer s = 0 := by
  have e : ∫ s in a..b, phiDer s = ∫ s in a..b, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [phiDer, max_eq_left (h s hs), mul_zero]
  rw [e]; simp

lemma integral_unit : ∫ s in (0 : ℝ)..1, phiDer s = 1 := by
  have h1 : ∫ s in (0 : ℝ)..1 / 4, phiDer s = 1 / 2 := by
    rw [integral_pos_piece]
    · rw [show 2 * π * (1 / 4 : ℝ) = π / 2 by ring]; simp
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact cos_nonneg_of_neg_pi_div_two_le_of_le (by nlinarith [pi_pos, hs.1])
        (by nlinarith [pi_pos, hs.2])
  have h2 : ∫ s in (1 / 4 : ℝ)..3 / 4, phiDer s = 0 := by
    refine integral_zero_piece fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    exact cos_nonpos_of_pi_div_two_le_of_le (by nlinarith [pi_pos, hs.1])
      (by nlinarith [pi_pos, hs.2])
  have h3 : ∫ s in (3 / 4 : ℝ)..1, phiDer s = 1 / 2 := by
    rw [integral_pos_piece]
    · rw [show 2 * π * (3 / 4 : ℝ) = 3 * π / 2 by ring, show 2 * π * (1 : ℝ) = 2 * π by ring]
      rw [show 3 * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two, sin_two_pi]; norm_num
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      have := cos_nonneg_of_neg_pi_div_two_le_of_le (x := 2 * π * s - 2 * π)
        (by nlinarith [pi_pos, hs.1]) (by nlinarith [pi_pos, hs.2])
      rwa [cos_sub_two_pi] at this
  have i : ∀ a b c : ℝ, (∫ s in a..b, phiDer s) + (∫ s in b..c, phiDer s) = ∫ s in a..c, phiDer s :=
    fun a b c => integral_add_adjacent_intervals (phiDer_continuous.intervalIntegrable _ _)
      (phiDer_continuous.intervalIntegrable _ _)
  rw [← i 0 (1 / 4) 1, ← i (1 / 4) (3 / 4) 1, h1, h2, h3]; norm_num

lemma phi_add_one (t : ℝ) : phi (t + 1) = phi t + 1 := by
  unfold phi
  have := integral_add_adjacent_intervals (a := 0) (b := t) (c := t + 1) (f := phiDer) (μ := volume)
    (phiDer_continuous.intervalIntegrable _ _) (phiDer_continuous.intervalIntegrable _ _)
  have h2 : ∫ s in t..t + 1, phiDer s = 1 := by
    rw [phiDer_periodic.intervalIntegral_add_eq t 0, zero_add, integral_unit]
  linarith

lemma phi_zero : phi 0 = 0 := by simp [phi]

lemma phi_mono : Monotone phi :=
  monotone_of_deriv_nonneg (fun t => (hasDerivAt_phi t).differentiableAt) fun t => by
    rw [deriv_phi]; exact phiDer_nonneg t

lemma phi_half : phi (1 / 2) = 1 / 2 := by
  unfold phi
  have h1 : ∫ s in (0 : ℝ)..1 / 4, phiDer s = 1 / 2 := by
    rw [integral_pos_piece]
    · rw [show 2 * π * (1 / 4 : ℝ) = π / 2 by ring]; simp
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact cos_nonneg_of_neg_pi_div_two_le_of_le (by nlinarith [pi_pos, hs.1])
        (by nlinarith [pi_pos, hs.2])
  have h2 : ∫ s in (1 / 4 : ℝ)..1 / 2, phiDer s = 0 := by
    refine integral_zero_piece fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    exact cos_nonpos_of_pi_div_two_le_of_le (by nlinarith [pi_pos, hs.1])
      (by nlinarith [pi_pos, hs.2])
  rw [← integral_add_adjacent_intervals (b := 1 / 4) (phiDer_continuous.intervalIntegrable _ _)
    (phiDer_continuous.intervalIntegrable _ _), h1, h2]; norm_num

lemma phi_one : phi 1 = 1 := by simpa [phi_zero] using phi_add_one 0

lemma periodic_phi_sub : Function.Periodic (fun t => phi t - t) 1 := fun t => by
  simp only [phi_add_one]; ring

lemma abs_phi_sub_le (t : ℝ) : |phi t - t| ≤ 1 / 2 := by
  obtain ⟨y, hy, e⟩ := periodic_phi_sub.exists_mem_Ico₀ one_pos t
  rw [e]
  have m0 := phi_mono hy.1
  rw [phi_zero] at m0
  rw [abs_le]
  rcases le_total y (1 / 2) with h | h
  · have := phi_mono h
    rw [phi_half] at this
    constructor <;> linarith [hy.1]
  · have := phi_mono h
    have := phi_mono hy.2.le
    rw [phi_half] at *
    rw [phi_one] at *
    constructor <;> linarith [hy.2]

lemma phi_int (n : ℤ) : phi n = n := by
  have := (periodic_phi_sub.int_mul n) 0
  simp only [zero_add, mul_one, phi_zero, sub_zero] at this
  linarith

/-- (existence, see `akalt_aux_phi`). -/
lemma exists_phi :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ (∀ n : ℤ, φ n = n) ∧ (∀ s, 0 ≤ deriv φ s) ∧
      (∃ ϖ : ℝ, ∀ s, deriv φ s ≤ ϖ) ∧ (∀ t, |φ t - t| ≤ 1 / 2) ∧
      ∀ s, deriv φ s * deriv φ (s + 1 / 2) = 0 := by
  refine ⟨phi, contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_phi t).differentiableAt, ?_⟩,
    phi_int, ?_, ⟨π, ?_⟩, abs_phi_sub_le, ?_⟩
  · rw [deriv_phi]; exact phiDer_continuous
  · intro s; rw [deriv_phi]; exact phiDer_nonneg s
  · intro s; rw [deriv_phi]; exact phiDer_le s
  · intro s; rw [deriv_phi]; exact phiDer_mul s

/-- The rescaling `s ↦ φ((n+1) s + a) / (n+1)`. -/
noncomputable def scl (φ : ℝ → ℝ) (n : ℕ) (a s : ℝ) : ℝ := φ (((n : ℝ) + 1) * s + a) / ((n : ℝ) + 1)

lemma scl_hasDerivAt {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (n : ℕ) (a s : ℝ) :
    HasDerivAt (scl φ n a) (deriv φ (((n : ℝ) + 1) * s + a)) s := by
  have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s => ((n : ℝ) + 1) * s + a) ((n : ℝ) + 1) s := by
    simpa using ((hasDerivAt_id s).const_mul ((n : ℝ) + 1)).add_const a
  have h2 := ((hφ.differentiable one_ne_zero) (((n : ℝ) + 1) * s + a)).hasDerivAt.comp s h1
  have h3 := h2.div_const ((n : ℝ) + 1)
  exact h3.congr_deriv (by field_simp)

lemma deriv_scl {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (n : ℕ) (a s : ℝ) :
    deriv (scl φ n a) s = deriv φ (((n : ℝ) + 1) * s + a) := (scl_hasDerivAt hφ n a s).deriv

lemma contDiff_scl {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (n : ℕ) (a : ℝ) :
    ContDiff ℝ 1 (scl φ n a) := by
  unfold scl
  exact (hφ.comp ((contDiff_const.mul contDiff_id).add contDiff_const)).div_const _

lemma abs_scl_sub_le {φ : ℝ → ℝ} (hc : ∀ t, |φ t - t| ≤ 1 / 2) (n : ℕ) (a s : ℝ) :
    |scl φ n a s - s| ≤ (1 / 2 + |a|) / ((n : ℝ) + 1) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have e : scl φ n a s - s =
      ((φ (((n : ℝ) + 1) * s + a) - (((n : ℝ) + 1) * s + a)) + a) / ((n : ℝ) + 1) := by
    unfold scl; field_simp; ring
  rw [e, abs_div, abs_of_pos hN]
  refine div_le_div_of_nonneg_right ?_ hN.le
  calc _ ≤ |φ (((n : ℝ) + 1) * s + a) - (((n : ℝ) + 1) * s + a)| + |a| := abs_add_le _ _
    _ ≤ _ := by linarith [hc (((n : ℝ) + 1) * s + a)]

end AFree.AKAltAux
