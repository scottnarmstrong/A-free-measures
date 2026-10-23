module

public import AFree.Harmonic.Kernel.Negative

/-!
# Truncated kernels

`m_L = m · (ψ₀ + Σ_{1 ≤ l ≤ L} ψ_l)` is a compactly supported smooth symbol; its kernel
`K_L = F⁻¹ m_L = Σ_{l ≤ L} K_l` is a Schwartz function, and `K_L ⋆ = vecMultiplier m_L`.
-/

@[expose] public section

open MeasureTheory PDE Filter
open scoped SchwartzMap ContDiff Topology

namespace AFree

noncomputable section

variable {d : ℕ}

theorem hasCompactSupport_lpCut (L : ℕ) : HasCompactSupport (lpCut (d := d) L) := by
  have : lpCut (d := d) L = fun ξ => lpPsi0 (((2 : ℝ)⁻¹) ^ L • ξ) := funext (lpCut_eq L)
  rw [this]
  refine (isCompact_vecNormSq_le (d := d) (2 * 2 ^ L)).of_isClosed_subset (isClosed_tsupport _) ?_
  apply closure_minimal
  · intro ξ hξ
    have hne : lpPsi0 (((2 : ℝ)⁻¹) ^ L • ξ) ≠ 0 := hξ
    have h1 : vecEuclideanNorm (((2 : ℝ)⁻¹) ^ L • ξ) ≤ 2 := by
      by_contra h
      exact hne (lpPsi0_eq_zero (by linarith [not_le.1 h]))
    rw [vecEuclideanNorm_smul, abs_of_nonneg (by positivity), inv_pow] at h1
    have hp : (0 : ℝ) < 2 ^ L := by positivity
    rw [inv_mul_le_iff₀ hp] at h1
    show vecNormSq ξ ≤ (2 * 2 ^ L) ^ 2
    have h2 := vecEuclideanNorm_sq ξ
    nlinarith [vecEuclideanNorm_nonneg ξ]
  · exact isClosed_le contDiff_vecNormSq.continuous continuous_const

theorem contDiff_lpTrunc {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (lpTrunc m L) :=
  hm.mul (Complex.ofRealCLM.contDiff.comp (contDiff_lpCut L))

theorem hasCompactSupport_lpTrunc (m : Vec d → ℂ) (L : ℕ) : HasCompactSupport (lpTrunc m L) := by
  refine (hasCompactSupport_lpCut (d := d) L).mono ?_
  intro ξ hξ
  simp only [lpTrunc, Function.mem_support, ne_eq, mul_eq_zero, not_or, Complex.ofReal_eq_zero]
    at hξ
  exact hξ.2

/-- The truncated symbol as a Schwartz function. -/
def lpTruncS {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) : 𝓢(Vec d, ℂ) :=
  (hasCompactSupport_lpTrunc m L).toSchwartzMap (by exact_mod_cast contDiff_lpTrunc hm L)

theorem lpTrunc_hasTemperateGrowth {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) :
    (lpTrunc m L).HasTemperateGrowth := (lpTruncS hm L).hasTemperateGrowth

theorem lpTrunc_eq_sum (m : Vec d → ℂ) (L : ℕ) (ξ : Vec d) :
    lpTrunc m L ξ = ∑ l ∈ Finset.range (L + 1), lpSym m l ξ := by
  simp [lpTrunc, lpSym, lpCut, Finset.mul_sum, Complex.ofReal_sum]

/-- The kernel of the truncated symbol. -/
def lpTruncKernel (m : Vec d → ℂ) (L : ℕ) : Vec d → ℂ := vecFourierInv (lpTrunc m L)

theorem lpTruncKernel_eq {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) :
    lpTruncKernel m L = ⇑(vecFourierInvCLM (lpTruncS hm L)) :=
  (vecFourierInv_coe (lpTruncS hm L)).symm

theorem lpTruncKernel_eq_sum {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) (x : Vec d) :
    lpTruncKernel m L x = ∑ l ∈ Finset.range (L + 1), lpKernel m l x := by
  unfold lpTruncKernel lpKernel
  simp only [vecFourierInv_def]
  rw [← integral_finsetSum]
  · congr 1
    funext ξ
    rw [← Finset.smul_sum]
    congr 1
    exact lpTrunc_eq_sum m L ξ
  · intro l _
    have : Integrable (lpSym m l) := (lpSymS hm l).integrable
    have h := integrable_fourierChar_smul this x
    simpa [vecDot_comm] using h

theorem contDiff_lpTruncKernel {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (lpTruncKernel m L) := by
  rw [lpTruncKernel_eq hm]; exact (vecFourierInvCLM _).smooth ⊤

theorem integrable_lpTruncKernel {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) :
    Integrable (lpTruncKernel m L) := by
  rw [lpTruncKernel_eq hm]; exact (vecFourierInvCLM _).integrable

theorem vecFourier_lpTruncKernel {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) :
    vecFourier (lpTruncKernel m L) = lpTrunc m L :=
  vecFourier_vecFourierInv (lpTruncS hm L)

/-- `K_L ⋆ f` is the multiplier with symbol `m_L`. -/
theorem vecMultiplier_lpTrunc {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ)
    (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    vecMultiplier (lpTrunc m L) f x = ∫ y, lpTruncKernel m L (x - y) * f y := by
  have h := vecMultiplier_vecFourier_apply (vecFourierInvCLM (lpTruncS hm L)) f x
  have e1 : vecFourier ⇑(vecFourierInvCLM (lpTruncS hm L)) = lpTrunc m L := by
    rw [← lpTruncKernel_eq hm L]; exact vecFourier_lpTruncKernel hm L
  rw [e1] at h
  rw [h]
  simp only [← lpTruncKernel_eq hm L]

end

end AFree
