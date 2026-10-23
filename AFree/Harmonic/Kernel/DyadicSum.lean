module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Dyadic sums

`Σ_l q^l (1 + 2^l r)^{-N} ≤ C r^{-a}` uniformly in the length of the sum, for `q = 2^a`, `0 < a < N`.
-/

@[expose] public section

namespace AFree

theorem two_rpow_pow_comm (x : ℝ) (k : ℕ) : ((2 : ℝ) ^ x) ^ k = ((2 : ℝ) ^ k) ^ x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 : ℝ) k,
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- The dyadic sum estimate. -/
theorem dyadic_sum_le {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : a < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ L : ℕ,
      ∑ l ∈ Finset.range L, ((2 : ℝ) ^ a) ^ l / (1 + 2 ^ l * r) ^ N ≤ C * r ^ (-a) := by
  set q : ℝ := (2 : ℝ) ^ a with hq
  set σ : ℝ := (2 : ℝ) ^ (a - N) with hσ
  have hq1 : 1 < q := Real.one_lt_rpow one_lt_two ha
  have hσ1 : σ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hσ0 : 0 < σ := by positivity
  have hq0 : 0 < q := by linarith
  refine ⟨q / (q - 1) + 1 / (1 - σ), by
    have : 0 < q - 1 := by linarith
    have : 0 < 1 - σ := by linarith
    positivity, fun r hr L => ?_⟩
  -- termwise bounds
  have hT1 : ∀ l : ℕ, q ^ l / (1 + 2 ^ l * r) ^ N ≤ q ^ l := fun l => by
    refine div_le_self (by positivity) ?_
    exact one_le_pow₀ (by have : (0 : ℝ) < 2 ^ l * r := by positivity
                          linarith)
  have hT2 : ∀ l : ℕ, q ^ l / (1 + 2 ^ l * r) ^ N ≤ r ^ (-(N : ℝ)) * σ ^ l := fun l => by
    have h1 : (2 ^ l * r) ^ N ≤ (1 + 2 ^ l * r) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    have h2 : q ^ l / (1 + 2 ^ l * r) ^ N ≤ q ^ l / (2 ^ l * r) ^ N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h1
    refine h2.trans (le_of_eq ?_)
    have hσl : σ ^ l = q ^ l / (2 ^ l) ^ N := by
      rw [hσ, hq, Real.rpow_sub (by norm_num), Real.rpow_natCast, div_pow, pow_right_comm]
    rw [hσl, Real.rpow_neg hr.le, Real.rpow_natCast, mul_pow, div_eq_mul_inv, div_eq_mul_inv,
      mul_inv]
    ring
  have hC1 : 0 ≤ q / (q - 1) := by
    have : 0 < q - 1 := by linarith
    positivity
  have hC2 : 0 ≤ 1 / (1 - σ) := by
    have : 0 < 1 - σ := by linarith
    positivity
  have hgeo : ∀ m n : ℕ, ∑ l ∈ Finset.Ico m n, σ ^ l ≤ σ ^ m / (1 - σ) :=
    fun m n => geom_sum_Ico_le_of_lt_one hσ0.le hσ1
  rcases lt_or_ge 1 r with hr1 | hr1
  · -- large `r`: every term is `≤ r^{-N} σ^l`
    calc ∑ l ∈ Finset.range L, q ^ l / (1 + 2 ^ l * r) ^ N
        ≤ ∑ l ∈ Finset.range L, r ^ (-(N : ℝ)) * σ ^ l := Finset.sum_le_sum fun l _ => hT2 l
      _ = r ^ (-(N : ℝ)) * ∑ l ∈ Finset.Ico 0 L, σ ^ l := by
          rw [Finset.mul_sum, Finset.range_eq_Ico]
      _ ≤ r ^ (-(N : ℝ)) * (σ ^ 0 / (1 - σ)) :=
          mul_le_mul_of_nonneg_left (hgeo 0 L) (by positivity)
      _ ≤ r ^ (-a) * (1 / (1 - σ)) := by
          rw [pow_zero]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hr1.le (by linarith)) hC2
      _ ≤ _ := by
          have : 0 ≤ q / (q - 1) * r ^ (-a) := mul_nonneg hC1 (by positivity)
          nlinarith
  · obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := 1 / r)
      (by rw [le_div_iff₀ hr]; linarith) one_lt_two
    have hnn : ∀ l : ℕ, 0 ≤ q ^ l / (1 + 2 ^ l * r) ^ N := fun l => by positivity
    have hq1' : q ≠ 1 := hq1.ne'
    have hgeoq : ∑ l ∈ Finset.range (k + 1), q ^ l ≤ q ^ k * (q / (q - 1)) := by
      rw [geom_sum_eq hq1']
      have : 0 < q - 1 := by linarith
      calc (q ^ (k + 1) - 1) / (q - 1) ≤ q ^ (k + 1) / (q - 1) :=
            div_le_div_of_nonneg_right (by linarith) this.le
        _ = q ^ k * (q / (q - 1)) := by rw [pow_succ]; ring
    have hqk : q ^ k ≤ r ^ (-a) := by
      rw [hq, two_rpow_pow_comm, Real.rpow_neg hr.le, ← Real.inv_rpow hr.le, ← one_div]
      exact Real.rpow_le_rpow (by positivity) hk1 ha.le
    have hσk : r ^ (-(N : ℝ)) * σ ^ (k + 1) ≤ r ^ (-a) := by
      have h1 : σ ^ (k + 1) ≤ (1 / r) ^ (a - N) := by
        rw [hσ, two_rpow_pow_comm]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hk2.le (by linarith)
      have h2 : (1 / r) ^ (a - N) = r ^ ((N : ℝ) - a) := by
        rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]; congr 1; ring
      calc r ^ (-(N : ℝ)) * σ ^ (k + 1) ≤ r ^ (-(N : ℝ)) * r ^ ((N : ℝ) - a) := by
            rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = r ^ (-a) := by rw [← Real.rpow_add hr]; congr 1; ring
    calc ∑ l ∈ Finset.range L, q ^ l / (1 + 2 ^ l * r) ^ N
        ≤ ∑ l ∈ Finset.range (k + 1 + L), q ^ l / (1 + 2 ^ l * r) ^ N :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            (fun l _ _ => hnn l)
      _ = ∑ l ∈ Finset.range (k + 1), q ^ l / (1 + 2 ^ l * r) ^ N +
          ∑ l ∈ Finset.Ico (k + 1) (k + 1 + L), q ^ l / (1 + 2 ^ l * r) ^ N :=
          (Finset.sum_range_add_sum_Ico _ (by omega)).symm
      _ ≤ ∑ l ∈ Finset.range (k + 1), q ^ l +
          ∑ l ∈ Finset.Ico (k + 1) (k + 1 + L), r ^ (-(N : ℝ)) * σ ^ l :=
          add_le_add (Finset.sum_le_sum fun l _ => hT1 l) (Finset.sum_le_sum fun l _ => hT2 l)
      _ ≤ q ^ k * (q / (q - 1)) + r ^ (-(N : ℝ)) * (σ ^ (k + 1) / (1 - σ)) := by
          rw [← Finset.mul_sum]
          exact add_le_add hgeoq (mul_le_mul_of_nonneg_left (hgeo _ _) (by positivity))
      _ ≤ r ^ (-a) * (q / (q - 1)) + r ^ (-a) * (1 / (1 - σ)) := by
          refine add_le_add (mul_le_mul_of_nonneg_right hqk hC1) ?_
          have hσk' : σ ^ (k + 1) * r ^ (-(N : ℝ)) ≤ r ^ (-a) := by rw [mul_comm]; exact hσk
          rw [← mul_div_assoc, ← mul_div_assoc, mul_one]
          exact div_le_div_of_nonneg_right hσk (by linarith)
      _ = _ := by ring

/-- A sequence dominated by `B` at `l = 0` and by `C₁ q^l (1 + 2^l r)^{-N}` for `l ≥ 1` has
partial sums bounded by `B + C₁ C_s r^{-a}`. -/
theorem sum_range_le_of_dyadic {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : a < N) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (w : ℕ → ℝ) (B C1 r : ℝ), 0 < r → 0 ≤ C1 → w 0 ≤ B →
      (∀ l, 0 ≤ w l) → (∀ l, 1 ≤ l → w l ≤ C1 * (((2 : ℝ) ^ a) ^ l / (1 + 2 ^ l * r) ^ N)) →
      ∀ n : ℕ, ∑ l ∈ Finset.range n, w l ≤ B + C1 * (Cs * r ^ (-a)) := by
  obtain ⟨Cs, hCs0, hCs⟩ := dyadic_sum_le ha hN
  refine ⟨Cs, hCs0, fun w B C1 r hr hC1 hB hw hwl n => ?_⟩
  have hB0 : 0 ≤ B := (hw 0).trans hB
  have hrC : 0 ≤ C1 * (Cs * r ^ (-a)) := mul_nonneg hC1 (mul_nonneg hCs0 (by positivity))
  rcases n with _ | n
  · simp; linarith
  · rw [Finset.sum_range_succ']
    have h1 : ∑ l ∈ Finset.range n, w (l + 1) ≤
        C1 * ∑ l ∈ Finset.range (n + 1), ((2 : ℝ) ^ a) ^ l / (1 + 2 ^ l * r) ^ N := by
      calc ∑ l ∈ Finset.range n, w (l + 1)
          ≤ ∑ l ∈ Finset.range n, C1 * (((2 : ℝ) ^ a) ^ (l + 1) / (1 + 2 ^ (l + 1) * r) ^ N) :=
            Finset.sum_le_sum fun l _ => hwl (l + 1) (by omega)
        _ = C1 * ∑ l ∈ Finset.range n, ((2 : ℝ) ^ a) ^ (l + 1) / (1 + 2 ^ (l + 1) * r) ^ N := by
            rw [Finset.mul_sum]
        _ ≤ C1 * ∑ l ∈ Finset.range (n + 1), ((2 : ℝ) ^ a) ^ l / (1 + 2 ^ l * r) ^ N := by
            refine mul_le_mul_of_nonneg_left ?_ hC1
            rw [Finset.sum_range_succ' _ n]
            have : 0 ≤ ((2 : ℝ) ^ a) ^ 0 / (1 + 2 ^ 0 * r) ^ N := by positivity
            linarith
    have h2 := mul_le_mul_of_nonneg_left (hCs r hr (n + 1)) hC1
    linarith

end AFree
