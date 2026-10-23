module

public import AFree.Curves.Defs
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Convolution

/-!
# Mollification `f(x) = ∫ ρ(y) g(x - y) dy`
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Convolution

namespace AFree

open PDE

variable {d : ℕ}

/-- The mollification `(g * ρ)(x) = ∫ ρ(y) g(x - y) dy` (Lebesgue measure on `Vec d`). -/
noncomputable def perturbMollify (ρ g : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ y, ρ y * g (x - y)

lemma perturbMollify_eq_convolution (ρ g : Vec d → ℝ) :
    perturbMollify ρ g = g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ := by
  rw [← convolution_flip]
  ext x
  simp [perturbMollify, convolution_def, mul_comm]

lemma perturbMollify_integrable {ρ g : Vec d → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hg : Continuous g) (x : Vec d) : Integrable (fun y => ρ y * g (x - y)) := by
  refine Continuous.integrable_of_hasCompactSupport (hρ.mul (hg.comp (continuous_const.sub continuous_id))) ?_
  exact hρc.mul_right

/-- For continuous `g` with `0 ≤ g ≤ ε` and a smooth, compactly
supported `ρ ≥ 0` with `∫ ρ = 1`, the mollification is `C^∞` and `0 ≤ g * ρ ≤ ε`. -/
theorem perturb_smooth_bounds {g ρ : Vec d → ℝ} {ε : ℝ} (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x ∧ g x ≤ ε) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1) :
    ContDiff ℝ (⊤ : ℕ∞) (perturbMollify ρ g) ∧ ∀ x, 0 ≤ perturbMollify ρ g x ∧
      perturbMollify ρ g x ≤ ε := by
  refine ⟨?_, fun x => ⟨integral_nonneg fun y => mul_nonneg (hρ0 y) (hg0 _).1, ?_⟩⟩
  · rw [perturbMollify_eq_convolution]
    exact hρc.contDiff_convolution_right _ (hg.locallyIntegrable (μ := volume)) hρ
  · have hint := perturbMollify_integrable hρ.continuous hρc hg x
    have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
    calc perturbMollify ρ g x ≤ ∫ y, ρ y * ε := by
          refine integral_mono hint (hρi.mul_const ε) fun y => ?_
          exact mul_le_mul_of_nonneg_left (hg0 _).2 (hρ0 y)
      _ = ε := by rw [integral_mul_const, hρ1, one_mul]

/-- Difference of mollifications: if `lo ≤ g(z + v) - g(z) ≤ hi` for `z = x - y`, `y ∈ supp ρ`, then
`lo ≤ (g * ρ)(x + v) - (g * ρ)(x) ≤ hi`. -/
theorem perturbMollify_sub_mem {g ρ : Vec d → ℝ} (hg : Continuous g) (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1) (x v : Vec d)
    {lo hi : ℝ} (h : ∀ y, ρ y ≠ 0 → lo ≤ g (x - y + v) - g (x - y) ∧
      g (x - y + v) - g (x - y) ≤ hi) :
    lo ≤ perturbMollify ρ g (x + v) - perturbMollify ρ g x ∧
      perturbMollify ρ g (x + v) - perturbMollify ρ g x ≤ hi := by
  have hρi : Integrable ρ := hρ.integrable_of_hasCompactSupport hρc
  have hi1 := perturbMollify_integrable hρ hρc hg (x + v)
  have hi2 := perturbMollify_integrable hρ hρc hg x
  have hdiff : perturbMollify ρ g (x + v) - perturbMollify ρ g x =
      ∫ y, ρ y * (g (x - y + v) - g (x - y)) := by
    unfold perturbMollify
    rw [← integral_sub hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [mul_sub]
    rw [show x + v - y = x - y + v by abel]
  rw [hdiff]
  have hint : Integrable fun y => ρ y * (g (x - y + v) - g (x - y)) := by
    have := hi1.sub hi2
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply, mul_sub]
    rw [show x + v - y = x - y + v by abel]
  constructor
  · calc lo = ∫ y, ρ y * lo := by rw [integral_mul_const, hρ1, one_mul]
      _ ≤ _ := by
        refine integral_mono (hρi.mul_const lo) hint fun y => ?_
        by_cases hy : ρ y = 0
        · simp [hy]
        · exact mul_le_mul_of_nonneg_left (h y hy).1 (hρ0 y)
  · calc _ ≤ ∫ y, ρ y * hi := by
          refine integral_mono hint (hρi.mul_const hi) fun y => ?_
          by_cases hy : ρ y = 0
          · simp [hy]
          · exact mul_le_mul_of_nonneg_left (h y hy).2 (hρ0 y)
      _ = hi := by rw [integral_mul_const, hρ1, one_mul]

end AFree
