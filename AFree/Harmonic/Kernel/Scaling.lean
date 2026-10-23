module

public import AFree.Harmonic.Fourier

/-!
# Scaling of the inverse Fourier transform

`F⁻¹ (f(c ·)) (x) = |c|^{-d} F⁻¹ f (x / c)`; consequently the `L¹` norm of `F⁻¹ (f(c ·))` equals
that of `F⁻¹ f`.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

noncomputable section

variable {d : ℕ}

theorem vecDot_smul_right (x y : Vec d) (c : ℝ) : vecDot x (c • y) = c * vecDot x y := by
  simp [vecDot, Finset.mul_sum, mul_left_comm]

theorem vecDot_smul_left (x y : Vec d) (c : ℝ) : vecDot (c • x) y = c * vecDot x y := by
  simp [vecDot, Finset.mul_sum, mul_assoc]

theorem vecFourierInv_comp_smul (f : Vec d → ℂ) {c : ℝ} (hc : c ≠ 0) (x : Vec d) :
    vecFourierInv (fun ξ => f (c • ξ)) x = |(c ^ d)⁻¹| • vecFourierInv f (c⁻¹ • x) := by
  have hfin : Module.finrank ℝ (Vec d) = d := by simp [Vec]
  have key : (fun ξ : Vec d => Real.fourierChar (vecDot ξ x) • f (c • ξ)) =
      fun ξ => (fun η : Vec d => Real.fourierChar (vecDot η (c⁻¹ • x)) • f η) (c • ξ) := by
    funext ξ
    simp only
    rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [vecFourierInv_def, key]
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Vec d)))
    (fun η : Vec d => Real.fourierChar (vecDot η (c⁻¹ • x)) • f η) c
  rw [hfin] at h
  exact h

theorem integral_norm_vecFourierInv_comp_smul (f : Vec d → ℂ) {c : ℝ} (hc : c ≠ 0) :
    ∫ x, ‖vecFourierInv (fun ξ => f (c • ξ)) x‖ = ∫ x, ‖vecFourierInv f x‖ := by
  have hfin : Module.finrank ℝ (Vec d) = d := by simp [Vec]
  simp_rw [vecFourierInv_comp_smul f hc, norm_smul, integral_const_mul]
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Vec d)))
    (fun y : Vec d => ‖vecFourierInv f y‖) c⁻¹
  rw [hfin] at h
  simp only [smul_eq_mul, Real.norm_eq_abs] at h ⊢
  rw [h, ← mul_assoc]
  have : |(c ^ d)⁻¹| * |((c⁻¹) ^ d)⁻¹| = 1 := by
    rw [← abs_mul, inv_pow, inv_inv, inv_mul_cancel₀ (pow_ne_zero _ hc), abs_one]
  rw [abs_abs, this, one_mul]

end

end AFree
