module

public import AFree.Harmonic.Kernel.GradSum

/-!
# Pointwise bounds for the negative-order kernel

For `m ∈ S^{-s}`, `K = Σ_l K_l`: `‖K x‖ ≤ C ‖x‖^{s-d}` when `0 < s < d`, bounded when `s > d`,
and `‖K x‖ ≤ C_M ‖x‖^{-M}` for `‖x‖ ≥ 1`.
-/

@[expose] public section

open MeasureTheory PDE Filter
open scoped SchwartzMap ContDiff Topology

namespace AFree

noncomputable section

variable {d : ℕ}

theorem norm_tsum_le_of_range_le {f : ℕ → ℂ} {c : ℝ}
    (h : ∀ n, ∑ l ∈ Finset.range n, ‖f l‖ ≤ c) : ‖∑' l, f l‖ ≤ c := by
  have hs : Summable fun l => ‖f l‖ := summable_of_sum_range_le (fun l => norm_nonneg _) h
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_of_sum_range_le h)

theorem one_pow_rpow_aux {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : a ≤ N) {r : ℝ} (hr : 0 < r) :
    r ^ a ≤ (1 + r) ^ N := by
  rcases le_total r 1 with h | h
  · calc r ^ a ≤ 1 := Real.rpow_le_one hr.le h ha
      _ ≤ (1 + r) ^ N := one_le_pow₀ (by linarith)
  · calc r ^ a ≤ r ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le h hN
      _ = r ^ N := Real.rpow_natCast r N
      _ ≤ (1 + r) ^ N := pow_le_pow_left₀ hr.le (by linarith) N

/-- `(2^l)^d (2^{-s})^l = (2^{d-s})^l`. -/
theorem two_pow_mul_aux (s : ℝ) (l : ℕ) :
    ((2 : ℝ) ^ l) ^ d * ((2 : ℝ) ^ (-s)) ^ l = ((2 : ℝ) ^ ((d : ℝ) - s)) ^ l := by
  rw [← pow_mul, mul_comm l d, pow_mul, ← mul_pow,
    show ((d : ℝ) - s) = (d : ℝ) + -s by ring, Real.rpow_add (by norm_num), Real.rpow_natCast]

/-- The size bound `‖K x‖ ≤ C ‖x‖^{s-d}` for `0 < s < d`. -/
theorem norm_negKernel_le {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {m : Vec d → ℂ}
    (hm : IsSymbol (-s) m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d, x ≠ 0 → ‖negKernel m x‖ ≤ C * ‖x‖ ^ (s - (d : ℝ)) := by
  set a : ℝ := (d : ℝ) - s with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hN : a < ((d : ℕ) : ℝ) := by rw [ha_def]; linarith
  obtain ⟨B0, hB0, hB⟩ := exists_weighted_lpKernel_zero hm.1 d
  obtain ⟨C1, hC1, hC⟩ := lpKernel_weighted_le hs0.le hm d
  obtain ⟨Cs, hCs0, hCs⟩ := sum_range_le_of_dyadic ha hN
  refine ⟨B0 + C1 * Cs, add_nonneg hB0 (mul_nonneg hC1 hCs0), fun x hx => ?_⟩
  set r : ℝ := ‖x‖ with hr
  have hrpos : 0 < r := norm_pos_iff.2 hx
  have hexp : s - (d : ℝ) = -a := by rw [ha_def]; ring
  have hmain : ∀ n, ∑ l ∈ Finset.range n, ‖lpKernel m l x‖ ≤
      B0 * r ^ (-a) + C1 * (Cs * r ^ (-a)) := by
    refine hCs (fun l => ‖lpKernel m l x‖) (B0 * r ^ (-a)) C1 r hrpos hC1 ?_
      (fun l => norm_nonneg _) ?_
    · have h := (hB x).1
      have hp : 0 < (1 + r) ^ d := by positivity
      have h1 : ‖lpKernel m 0 x‖ ≤ B0 / (1 + r) ^ d := by rw [le_div_iff₀ hp]; linarith
      refine h1.trans ?_
      rw [Real.rpow_neg hrpos.le, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ hB0
      exact inv_anti₀ (by positivity) (one_pow_rpow_aux ha.le hN.le hrpos)
    · intro l hl
      have h := (hC l hl x).1
      rw [← hr] at h
      have hp : 0 < (1 + 2 ^ l * r) ^ d := by positivity
      rw [mul_assoc, two_pow_mul_aux] at h
      rw [← mul_div_assoc, le_div_iff₀ hp, mul_comm]
      exact h
  have := norm_tsum_le_of_range_le hmain
  refine this.trans (le_of_eq ?_)
  rw [hexp]; ring

/-- Rapid decay `‖K x‖ ≤ C_M ‖x‖^{-M}` for `‖x‖ ≥ 1`. -/
theorem norm_negKernel_le_decay {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {m : Vec d → ℂ}
    (hm : IsSymbol (-s) m) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d, 1 ≤ ‖x‖ → ‖x‖ ^ M * ‖negKernel m x‖ ≤ C := by
  set a : ℝ := (d : ℝ) - s with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hN : a < ((d : ℕ) : ℝ) := by rw [ha_def]; linarith
  obtain ⟨B0, hB0, hB⟩ := exists_weighted_lpKernel_zero hm.1 M
  obtain ⟨C1, hC1, hC⟩ := lpKernel_weighted_le hs0.le hm (M + d)
  obtain ⟨Cs, hCs0, hCs⟩ := sum_range_le_of_dyadic ha hN
  refine ⟨B0 + C1 * Cs, add_nonneg hB0 (mul_nonneg hC1 hCs0), fun x hx1 => ?_⟩
  set r : ℝ := ‖x‖ with hr
  have hrpos : 0 < r := by linarith
  have hrM : 0 ≤ r ^ M := by positivity
  have hmain : ∀ n, ∑ l ∈ Finset.range n, ‖((r ^ M : ℝ) : ℂ) * lpKernel m l x‖ ≤
      B0 + C1 * (Cs * r ^ (-a)) := by
    intro n
    have := hCs (fun l => ‖((r ^ M : ℝ) : ℂ) * lpKernel m l x‖) B0 C1 r hrpos hC1 ?_
      (fun l => norm_nonneg _) ?_ n
    · simpa using this
    · have h := (hB x).1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hrM]
      refine le_trans ?_ h
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hrpos.le (by linarith) M) (norm_nonneg _)
    · intro l hl
      have h := (hC l hl x).1
      rw [← hr] at h
      have hp : 0 < (1 + 2 ^ l * r) ^ d := by positivity
      rw [mul_assoc, two_pow_mul_aux] at h
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hrM, ← mul_div_assoc,
        le_div_iff₀ hp]
      have h2 : r ^ M ≤ (1 + 2 ^ l * r) ^ M :=
        pow_le_pow_left₀ hrpos.le (by have : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
                                      nlinarith) M
      calc r ^ M * ‖lpKernel m l x‖ * (1 + 2 ^ l * r) ^ d
          ≤ (1 + 2 ^ l * r) ^ M * ‖lpKernel m l x‖ * (1 + 2 ^ l * r) ^ d := by gcongr
        _ = (1 + 2 ^ (l) * r) ^ (M + d) * ‖lpKernel m l x‖ := by rw [pow_add]; ring
        _ ≤ _ := h
  have h1 := norm_tsum_le_of_range_le hmain
  rw [tsum_mul_left] at h1
  have hneg : r ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have h3 : B0 + C1 * (Cs * r ^ (-a)) ≤ B0 + C1 * Cs := by
    have : Cs * r ^ (-a) ≤ Cs * 1 := mul_le_mul_of_nonneg_left hneg hCs0
    nlinarith
  refine le_trans (le_of_eq ?_) (h1.trans h3)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hrM]
  rfl

/-- For any `s > 0` (also `s ≥ d`) and any `t` with `0 < t < d`, `t ≤ s`: `‖K x‖ ≤ C ‖x‖^{t-d}`. -/
theorem norm_negKernel_le_of_le {s t : ℝ} (ht0 : 0 < t) (htd : t < d) (hts : t ≤ s)
    {m : Vec d → ℂ} (hm : IsSymbol (-s) m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d, x ≠ 0 → ‖negKernel m x‖ ≤ C * ‖x‖ ^ (t - (d : ℝ)) :=
  norm_negKernel_le ht0 htd (hm.mono (by linarith))

/-- Rapid decay for any `s > 0` when `d > 0`. -/
theorem norm_negKernel_le_decay_of_pos (hd : 0 < d) {s : ℝ} (hs0 : 0 < s) {m : Vec d → ℂ}
    (hm : IsSymbol (-s) m) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d, 1 ≤ ‖x‖ → ‖x‖ ^ M * ‖negKernel m x‖ ≤ C := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ht0 : 0 < min s ((d : ℝ) / 2) := lt_min hs0 (by positivity)
  have htd : min s ((d : ℝ) / 2) < d := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  exact norm_negKernel_le_decay ht0 htd (hm.mono (by have := min_le_left s ((d : ℝ) / 2); linarith)) M

end

end AFree
