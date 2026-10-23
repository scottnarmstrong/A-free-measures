module

public import AFree.Harmonic.Kernel.Real

/-!
# Order-zero symbols give uniform Hörmander kernels

For `m ∈ S⁰` with real kernels (`m(-ξ) = conj m(ξ)`), the real truncated kernels
`K_L = Re F⁻¹ (m · (ψ₀ + Σ_{1 ≤ l ≤ L} ψ_l))` are smooth, integrable, satisfy an `L²` bound and the
Hörmander gradient bound with a constant `A` independent of `L`, and `K_L ⋆ f → vecMultiplier m f`
pointwise and in `L²` for Schwartz `f`. These are exactly the hypotheses of
`exists_weakTypeOne_of_hormander`.
-/

@[expose] public section

open MeasureTheory PDE Filter
open scoped SchwartzMap ContDiff Topology ComplexConjugate

namespace AFree

noncomputable section

variable {d : ℕ}

/-- Uniform Hörmander data for the truncations of an order-zero symbol with real kernels. -/
theorem exists_uniform_hormander_kernels {m : Vec d → ℂ} (hm : IsSymbol 0 m)
    (hreal : ∀ ξ, m (-ξ) = conj (m ξ)) :
    ∃ A : ℝ, 0 ≤ A ∧ (∀ ξ, ‖m ξ‖ ≤ A) ∧ ∀ L : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (realKernel m L) ∧ Integrable (realKernel m L) ∧
      (∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ∫ x, (∫ y, realKernel m L (x - y) * f y) ^ 2 ≤ A ^ 2 * ∫ x, f x ^ 2) ∧
      (∀ x : Vec d, x ≠ 0 → ∀ v : Vec d,
        |fderiv ℝ (realKernel m L) x v| ≤ A * vecEuclideanNorm v / vecEuclideanNorm x ^ (d + 1)) := by
  obtain ⟨A1, hA1, hA1b⟩ := hm.exists_norm_le_zero
  obtain ⟨A2, hA2, hA2b⟩ := abs_fderiv_realKernel_le hm
  refine ⟨max A1 A2, le_max_of_le_left hA1, fun ξ => (hA1b ξ).trans (le_max_left _ _),
    fun L => ⟨contDiff_realKernel hm.1 L, integrable_realKernel hm.1 L, ?_, ?_⟩⟩
  · intro f hf hc
    refine (integral_sq_realKernel_conv_le hm.1 hreal hA1b L f hf hc).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun x => sq_nonneg _)
    exact pow_le_pow_left₀ hA1 (le_max_left _ _) 2
  · intro x hx v
    refine (hA2b L x v hx).trans ?_
    have hxe : 0 < vecEuclideanNorm x ^ (d + 1) := by
      have : 0 < ‖x‖ := norm_pos_iff.2 hx
      have h2 := norm_le_vecEuclideanNorm x
      exact pow_pos (by linarith) _
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (vecEuclideanNorm_nonneg v)) hxe.le

/-- Pointwise convergence `K_L ⋆ f → vecMultiplier m f` for the real kernels. -/
theorem tendsto_realKernel_conv {m : Vec d → ℂ} (hm : IsSymbol 0 m)
    (hreal : ∀ ξ, m (-ξ) = conj (m ξ)) (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    Tendsto (fun L => ∫ y, ((realKernel m L (x - y) : ℝ) : ℂ) * f y) atTop
      (𝓝 (vecMultiplier m f x)) := by
  simpa [realKernel_coe hreal] using tendsto_lpTruncKernel_conv hm.hasTemperateGrowth f x

end

end AFree
