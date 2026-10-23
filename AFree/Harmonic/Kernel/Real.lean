module

public import AFree.Harmonic.Kernel.Order0
public import AFree.Harmonic.Kernel.GradSum

/-!
# Real kernels
-/

@[expose] public section

open MeasureTheory PDE Filter
open scoped SchwartzMap ContDiff Topology ComplexConjugate

namespace AFree

noncomputable section

variable {d : ℕ}

theorem vecDot_neg_left (x y : Vec d) : vecDot (-x) y = -vecDot x y := by
  simp [vecDot, Finset.sum_neg_distrib]

theorem conj_fourierChar_smul (t : ℝ) (z : ℂ) :
    conj (Real.fourierChar t • z) = Real.fourierChar (-t) • conj z := by
  simp only [Circle.smul_def, smul_eq_mul, map_mul]
  congr 1
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem conj_vecFourierInv_of_real (f : Vec d → ℂ) (hf : ∀ ξ, f (-ξ) = conj (f ξ)) (x : Vec d) :
    conj (vecFourierInv f x) = vecFourierInv f x := by
  rw [vecFourierInv_def, ← integral_conj]
  conv_rhs => rw [← integral_neg_eq_self]
  congr 1
  funext ξ
  rw [conj_fourierChar_smul, vecDot_neg_left, hf]

theorem lpPsi0_neg (ξ : Vec d) : lpPsi0 (-ξ) = lpPsi0 ξ := by
  unfold lpPsi0 euclideanCutoff
  rw [vecNormSq_neg]

theorem lpCut_neg (L : ℕ) (ξ : Vec d) : lpCut L (-ξ) = lpCut L ξ := by
  rw [lpCut_eq, lpCut_eq, smul_neg, lpPsi0_neg]

theorem lpTrunc_neg {m : Vec d → ℂ} (hreal : ∀ ξ, m (-ξ) = conj (m ξ)) (L : ℕ) (ξ : Vec d) :
    lpTrunc m L (-ξ) = conj (lpTrunc m L ξ) := by
  simp only [lpTrunc, hreal, lpCut_neg, map_mul, Complex.conj_ofReal]

theorem conj_lpTruncKernel {m : Vec d → ℂ} (hreal : ∀ ξ, m (-ξ) = conj (m ξ)) (L : ℕ) (x : Vec d) :
    conj (lpTruncKernel m L x) = lpTruncKernel m L x :=
  conj_vecFourierInv_of_real _ (lpTrunc_neg hreal L) x

/-- The real kernel `K_L = Re F⁻¹ m_L`. -/
def realKernel (m : Vec d → ℂ) (L : ℕ) : Vec d → ℝ := fun x => (lpTruncKernel m L x).re

theorem realKernel_coe {m : Vec d → ℂ} (hreal : ∀ ξ, m (-ξ) = conj (m ξ)) (L : ℕ) (x : Vec d) :
    ((realKernel m L x : ℝ) : ℂ) = lpTruncKernel m L x := by
  have h := conj_lpTruncKernel hreal L x
  rw [Complex.conj_eq_iff_re] at h
  exact h

theorem contDiff_realKernel {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (realKernel m L) :=
  Complex.reCLM.contDiff.comp (contDiff_lpTruncKernel hm L)

theorem integrable_realKernel {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ) :
    Integrable (realKernel m L) :=
  (integrable_lpTruncKernel hm L).re

theorem integral_sq_realKernel_conv_le {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hreal : ∀ ξ, m (-ξ) = conj (m ξ)) {A : ℝ} (hA : ∀ ξ, ‖m ξ‖ ≤ A) (L : ℕ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∫ x, (∫ y, realKernel m L (x - y) * f y) ^ 2 ≤ A ^ 2 * ∫ x, f x ^ 2 := by
  have h := integral_norm_sq_lpTruncKernel_conv_le hm hA L (toSchwartzC f hf hc)
  have e1 : ∀ x, ∫ y, lpTruncKernel m L (x - y) * (toSchwartzC f hf hc) y =
      ((∫ y, realKernel m L (x - y) * f y : ℝ) : ℂ) := by
    intro x
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [realKernel_coe hreal]
  have e2 : ∀ x, ‖((∫ y, realKernel m L (x - y) * f y : ℝ) : ℂ)‖ ^ 2 =
      (∫ y, realKernel m L (x - y) * f y) ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e3 : ∀ x, ‖(toSchwartzC f hf hc) x‖ ^ 2 = f x ^ 2 := fun x => by
    rw [toSchwartzC_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [e1, e2, e3] at h
  exact h

theorem abs_fderiv_realKernel_le {m : Vec d → ℂ} (hm : IsSymbol 0 m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (L : ℕ) (x v : Vec d), x ≠ 0 →
      |fderiv ℝ (realKernel m L) x v| ≤ A * vecEuclideanNorm v / vecEuclideanNorm x ^ (d + 1) := by
  obtain ⟨A0, hA0, hA⟩ := exists_fderiv_sum_lpKernel_le hm
  refine ⟨A0 * Real.sqrt d ^ (d + 1), by positivity, fun L x v hx => ?_⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hxe : 0 < vecEuclideanNorm x := by
    have := norm_le_vecEuclideanNorm x; linarith
  have hK : lpTruncKernel m L = fun y => ∑ l ∈ Finset.range (L + 1), lpKernel m l y :=
    funext (lpTruncKernel_eq_sum hm.1 L)
  have hdiff : DifferentiableAt ℝ (lpTruncKernel m L) x := by
    rw [lpTruncKernel_eq hm.1]; exact (vecFourierInvCLM _).differentiableAt
  have hf : fderiv ℝ (realKernel m L) x = Complex.reCLM.comp (fderiv ℝ (lpTruncKernel m L) x) :=
    (Complex.reCLM.hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv
  have h1 : |fderiv ℝ (realKernel m L) x v| ≤ ‖fderiv ℝ (lpTruncKernel m L) x‖ * ‖v‖ := by
    rw [hf]
    refine (Complex.abs_re_le_norm _).trans ?_
    exact (fderiv ℝ (lpTruncKernel m L) x).le_opNorm v
  have h2 : ‖fderiv ℝ (lpTruncKernel m L) x‖ ≤ A0 * ‖x‖ ^ (-((d : ℝ) + 1)) := by
    rw [hK]; exact hA L x hx
  have hneg : ‖x‖ ^ (-((d : ℝ) + 1)) = (‖x‖ ^ (d + 1))⁻¹ := by
    rw [Real.rpow_neg hxn.le, show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have h3 : vecEuclideanNorm x ≤ Real.sqrt d * ‖x‖ := vecEuclideanNorm_le_sqrt_natCast_mul_norm x
  have h4 : (‖x‖ ^ (d + 1))⁻¹ ≤ Real.sqrt d ^ (d + 1) / vecEuclideanNorm x ^ (d + 1) := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ hxe.le h3 _
  have h5 : ‖v‖ ≤ vecEuclideanNorm v := norm_le_vecEuclideanNorm v
  calc |fderiv ℝ (realKernel m L) x v| ≤ ‖fderiv ℝ (lpTruncKernel m L) x‖ * ‖v‖ := h1
    _ ≤ (A0 * (Real.sqrt d ^ (d + 1) / vecEuclideanNorm x ^ (d + 1))) * vecEuclideanNorm v := by
        refine mul_le_mul ?_ h5 (norm_nonneg _) (by positivity)
        refine h2.trans (mul_le_mul_of_nonneg_left ?_ hA0)
        rw [hneg]; exact h4
    _ = _ := by ring

end

end AFree
