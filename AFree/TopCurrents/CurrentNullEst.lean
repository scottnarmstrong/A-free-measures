module

public import AFree.TopCurrents.Basic

/-!
# The cut-off estimate for the vanishing of `ν` on compact null sets

If `h = f · D_e g` with `f` a cut-off of `K`, `g` with `D_e g = 1` near `K` and `0 ≤ D_e g ≤ 1`, then
`|∫ h dν − ν(K)| ≤ |ν|(V ∖ K)` where `V ⊇ {f ≠ 0}`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.Nu

/-- (estimate) `|ν(K)| ≤ |ν|(V ∖ K) + |∫ f D_e g dν|`. -/
theorem currentnull_estimate {d : ℕ} (ν : SignedMeasure (Vec d)) {e : Vec d} {K : Set (Vec d)}
    (hK : IsCompact K) {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hD : ∀ x, 0 ≤ fderiv ℝ g x e ∧ fderiv ℝ g x e ≤ 1)
    (hU : ∃ U : Set (Vec d), IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, fderiv ℝ g x e = 1)
    {f : Vec d → ℝ} (hf : IsBddLipFun f) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hfK : ∀ x ∈ K, f x = 1) {V : Set (Vec d)} (hVm : MeasurableSet V)
    (hfV : ∀ x, f x ≠ 0 → x ∈ V) :
    |ν K| ≤ (ν.variation (V \ K)).toReal + |∫ᵛ x, f x * fderiv ℝ g x e ∂•ν| := by
  have hfin := finite_variation ν
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  obtain ⟨U, -, hKU, hUe⟩ := hU
  have hfB := isBorelBdd_of_isBddLipFun hf
  have hDc : Continuous fun x => fderiv ℝ g x e :=
    ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hhB : IsBorelBdd fun x => f x * fderiv ℝ g x e :=
    ⟨hfB.1.mul hDc.measurable, 1, fun x => by
      rw [abs_of_nonneg (mul_nonneg (hf01 x).1 (hD x).1)]
      calc f x * fderiv ℝ g x e ≤ 1 * 1 :=
            mul_le_mul (hf01 x).2 (hD x).2 (hD x).1 zero_le_one
        _ = 1 := one_mul 1⟩
  have hKint : ν K = ∫ᵛ x, K.indicator (fun _ => (1 : ℝ)) x ∂•ν := by
    have h2 := VectorMeasure.integral_indicator_const
      (B := ContinuousLinearMap.lsmul ℝ ℝ) (μ := ν) (1 : ℝ) hKm
    simpa using h2.symm
  have hIK : IsBorelBdd (K.indicator (fun _ => (1 : ℝ))) := by
    have := isBorelBdd_indicator (d := d) hKm
    convert this using 1
  have hi1 : ν.Integrable fun x => f x * fderiv ℝ g x e := integrable_of_isBorelBdd hhB
  have hi2 : ν.Integrable (K.indicator fun _ => (1 : ℝ)) := integrable_of_isBorelBdd hIK
  have hsub : ∫ᵛ x, f x * fderiv ℝ g x e ∂•ν - ν K =
      ∫ᵛ x, (f x * fderiv ℝ g x e - K.indicator (fun _ => (1 : ℝ)) x) ∂•ν := by
    rw [hKint]
    exact (VectorMeasure.integral_fun_sub hi1 hi2).symm
  have hpt : ∀ x, |f x * fderiv ℝ g x e - K.indicator (fun _ => (1 : ℝ)) x| ≤
      (V \ K).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hxK : x ∈ K
    · have h1 := hfK x hxK
      have h2 := hUe x (hKU hxK)
      simp [hxK, h1, h2]
    · by_cases hxV : x ∈ V
      · have hx : x ∈ V \ K := ⟨hxV, hxK⟩
        simp only [hxK, hx, Set.indicator_of_notMem, Set.indicator_of_mem, sub_zero, not_false_eq_true]
        rw [abs_of_nonneg (mul_nonneg (hf01 x).1 (hD x).1)]
        calc f x * fderiv ℝ g x e ≤ 1 * 1 :=
              mul_le_mul (hf01 x).2 (hD x).2 (hD x).1 zero_le_one
          _ = 1 := one_mul 1
      · have : f x = 0 := by
          by_contra hne
          exact hxV (hfV x hne)
        simp [hxK, hxV, this]
  have hbound : |∫ᵛ x, f x * fderiv ℝ g x e ∂•ν - ν K| ≤ (ν.variation (V \ K)).toReal := by
    rw [hsub]
    refine (abs_integral_le ν _).trans ?_
    have hVK : MeasurableSet (V \ K) := hVm.diff hKm
    have hint : Integrable ((V \ K).indicator fun _ => (1 : ℝ)) ν.variation :=
      (integrable_const (1 : ℝ)).indicator hVK
    have hint2 : Integrable (fun x => |f x * fderiv ℝ g x e - K.indicator (fun _ => (1 : ℝ)) x|)
        ν.variation := (hi1.sub hi2).abs
    calc ∫ x, |f x * fderiv ℝ g x e - K.indicator (fun _ => (1 : ℝ)) x| ∂ν.variation
        ≤ ∫ x, (V \ K).indicator (fun _ => (1 : ℝ)) x ∂ν.variation :=
          integral_mono hint2 hint hpt
      _ = (ν.variation (V \ K)).toReal := by
          rw [integral_indicator_const _ hVK]
          simp [Measure.real]
  have h3 : |ν K| - |∫ᵛ x, f x * fderiv ℝ g x e ∂•ν| ≤ |ν K - ∫ᵛ x, f x * fderiv ℝ g x e ∂•ν| :=
    abs_sub_abs_le_abs_sub _ _
  rw [abs_sub_comm] at h3
  linarith

end AFree
