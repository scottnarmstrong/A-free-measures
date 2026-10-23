module

public import AFree.Harmonic.Kernel.Pointwise
public import AFree.Harmonic.Kernel.DyadicSum
public import AFree.Harmonic.Kernel.Negative

/-!
# Summing the dyadic kernel estimates

Uniform (in `L`) Hörmander-type gradient bound for `Σ_{l ≤ L} K_l` when `m ∈ S⁰`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap ContDiff

namespace AFree

noncomputable section

variable {d : ℕ}

theorem differentiable_lpKernel {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ) :
    Differentiable ℝ (lpKernel m l) := by
  rw [lpKernel_eq hm]; exact (vecFourierInvCLM _).differentiable

/-- The zeroth piece is a fixed Schwartz function with `(1 + ‖x‖)^N`-weighted bounds. -/
theorem exists_weighted_lpKernel_zero {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec d,
      (1 + ‖x‖) ^ N * ‖lpKernel m 0 x‖ ≤ B ∧
      (1 + ‖x‖) ^ N * ‖fderiv ℝ (lpKernel m 0) x‖ ≤ B := by
  obtain ⟨s0, C0, hC0, hC⟩ := exists_vecFourierInv_weighted_le d N
  refine ⟨C0 * (s0.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) (lpSymS hm 0),
    mul_nonneg hC0 (apply_nonneg _ _), fun x => ?_⟩
  have h := hC (lpSymS hm 0) x
  exact ⟨h.1, h.2⟩

theorem exists_fderiv_sum_lpKernel_le {m : Vec d → ℂ} (hm : IsSymbol 0 m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (L : ℕ) (x : Vec d), x ≠ 0 →
      ‖fderiv ℝ (fun y => ∑ l ∈ Finset.range (L + 1), lpKernel m l y) x‖ ≤
        A * ‖x‖ ^ (-((d : ℝ) + 1)) := by
  obtain ⟨B0, hB0, hB⟩ := exists_weighted_lpKernel_zero hm.1 (d + 1)
  obtain ⟨C, hC0, hC⟩ := lpKernel_weighted_le (le_refl (0 : ℝ)) (by simpa using hm) (d + 2)
  have ha : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hN : (d : ℝ) + 1 < ((d + 2 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨Cs, hCs0, hCs⟩ := dyadic_sum_le ha hN
  refine ⟨B0 + C * Cs, add_nonneg hB0 (mul_nonneg hC0 hCs0), fun L x hx => ?_⟩
  set r : ℝ := ‖x‖ with hr
  have hrpos : 0 < r := norm_pos_iff.2 hx
  rw [fderiv_fun_sum (fun l _ => (differentiable_lpKernel hm.1 l).differentiableAt)]
  rw [Finset.sum_range_succ']
  refine (norm_add_le _ _).trans ?_
  have hneg : r ^ (-((d : ℝ) + 1)) = (r ^ (d + 1))⁻¹ := by
    rw [Real.rpow_neg hrpos.le, show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have h0 : ‖fderiv ℝ (lpKernel m 0) x‖ ≤ B0 * r ^ (-((d : ℝ) + 1)) := by
    have := (hB x).2
    have hp : 0 < (1 + r) ^ (d + 1) := by positivity
    have h1 : ‖fderiv ℝ (lpKernel m 0) x‖ ≤ B0 / (1 + r) ^ (d + 1) := by
      rw [le_div_iff₀ hp]; linarith
    refine h1.trans ?_
    rw [hneg, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hrpos.le (by linarith) _)
  have hT : ∀ l : ℕ, ‖fderiv ℝ (lpKernel m (l + 1)) x‖ ≤
      C * ((2 : ℝ) ^ (((d : ℝ) + 1))) ^ (l + 1) / (1 + 2 ^ (l + 1) * r) ^ (d + 2) := by
    intro l
    have h := (hC (l + 1) (by omega) x).2
    simp only [neg_zero, Real.rpow_zero, one_pow, mul_one] at h
    rw [← hr] at h
    have hp : 0 < (1 + 2 ^ (l + 1) * r) ^ (d + 2) := by positivity
    have hq : ((2 : ℝ) ^ ((d : ℝ) + 1)) ^ (l + 1) = ((2 : ℝ) ^ (l + 1)) ^ (d + 1) := by
      rw [two_rpow_pow_comm, show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [hq, le_div_iff₀ hp, mul_comm]
    exact h
  have hsum : ∑ l ∈ Finset.range L, ‖fderiv ℝ (lpKernel m (l + 1)) x‖ ≤
      C * (Cs * r ^ (-((d : ℝ) + 1))) := by
    calc ∑ l ∈ Finset.range L, ‖fderiv ℝ (lpKernel m (l + 1)) x‖
        ≤ ∑ l ∈ Finset.range L, C * (((2 : ℝ) ^ (((d : ℝ) + 1))) ^ (l + 1) /
            (1 + 2 ^ (l + 1) * r) ^ (d + 2)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [← mul_div_assoc]; exact hT l
      _ = C * ∑ l ∈ Finset.range L, ((2 : ℝ) ^ (((d : ℝ) + 1))) ^ (l + 1) /
            (1 + 2 ^ (l + 1) * r) ^ (d + 2) := by rw [Finset.mul_sum]
      _ ≤ C * ∑ l ∈ Finset.range (L + 1), ((2 : ℝ) ^ (((d : ℝ) + 1))) ^ l /
            (1 + 2 ^ l * r) ^ (d + 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          rw [Finset.sum_range_succ']
          have : 0 ≤ ((2 : ℝ) ^ (((d : ℝ) + 1))) ^ 0 / (1 + 2 ^ 0 * r) ^ (d + 2) := by positivity
          linarith
      _ ≤ C * (Cs * r ^ (-((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (hCs r hrpos (L + 1)) hC0
  have := norm_sum_le (Finset.range L) fun l => fderiv ℝ (lpKernel m (l + 1)) x
  calc _ ≤ _ := add_le_add this h0
    _ ≤ (C * (Cs * r ^ (-((d : ℝ) + 1)))) + B0 * r ^ (-((d : ℝ) + 1)) := add_le_add hsum le_rfl
    _ = _ := by rw [hr]; ring

end

end AFree
