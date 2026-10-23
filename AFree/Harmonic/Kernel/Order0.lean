module

public import AFree.Harmonic.Kernel.Truncated

/-!
# Order-zero symbols: `L²` bounds and convergence of the truncated kernels

For `m ∈ S⁰`: `‖m_L‖_∞ ≤ A` (independent of `L`), hence `‖K_L ⋆ f‖₂ ≤ A ‖f‖₂`, and
`K_L ⋆ f → vecMultiplier m f` pointwise and in `L²` for Schwartz `f`.
-/

@[expose] public section

open MeasureTheory PDE Filter
open scoped SchwartzMap ContDiff Topology

namespace AFree

noncomputable section

variable {d : ℕ}

theorem IsSymbol.exists_norm_le_zero {m : Vec d → ℂ} (hm : IsSymbol 0 m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ, ‖m ξ‖ ≤ A := by
  obtain ⟨C, hC0, hC⟩ := (hm.bound 0).nonneg
  refine ⟨C, hC0, fun ξ => ?_⟩
  have := hC ξ
  simpa using this

theorem norm_lpTrunc_le {m : Vec d → ℂ} {A : ℝ} (hA : ∀ ξ, ‖m ξ‖ ≤ A) (L : ℕ) (ξ : Vec d) :
    ‖lpTrunc m L ξ‖ ≤ A := by
  unfold lpTrunc
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lpCut_nonneg L ξ)]
  have h1 := lpCut_le_one L ξ
  have h2 := hA ξ
  have : 0 ≤ ‖m ξ‖ := norm_nonneg _
  nlinarith

/-- `L²` bound for the truncated kernels, uniform in `L`. -/
theorem integral_norm_sq_lpTruncKernel_conv_le {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) {A : ℝ}
    (hA : ∀ ξ, ‖m ξ‖ ≤ A) (L : ℕ) (f : 𝓢(Vec d, ℂ)) :
    ∫ x, ‖∫ y, lpTruncKernel m L (x - y) * f y‖ ^ 2 ≤ A ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  have h := integral_norm_sq_vecMultiplier_le (lpTrunc_hasTemperateGrowth hm L)
    (norm_lpTrunc_le hA L) f
  simpa [vecMultiplier_lpTrunc hm L f] using h

/-- Pointwise convergence `K_L ⋆ f → vecMultiplier m f`. -/
theorem tendsto_lpTruncKernel_conv {m : Vec d → ℂ} (hm : m.HasTemperateGrowth)
    (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    Tendsto (fun L => ∫ y, lpTruncKernel m L (x - y) * f y) atTop (𝓝 (vecMultiplier m f x)) := by
  have h := tendsto_sum_vecMultiplier_lpSym hm f x
  refine h.congr fun L => ?_
  rw [← vecMultiplier_lpTrunc hm.1 L f x,
    vecMultiplier_apply_integral (lpTrunc_hasTemperateGrowth hm.1 L),
    sum_vecMultiplier_lpSym hm.1 L f x]
  rfl

end

end AFree
