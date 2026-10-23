module

public import AFree.Paper.BD.SaintVenant
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Kernel of the Saint-Venant symbol on symmetric matrices

For `|ξ| = 1`, a symmetric matrix `M` is annihilated by the Saint-Venant symbol iff `M = a ⊗ ξ + ξ ⊗ a`
for some `a`; this is used in the proof of [DPR, Theorem 1.7].
-/

public section

open Matrix PDE

namespace AFree

variable {d : ℕ}

/-- Components of `𝔸₂(ξ) M` for the Saint-Venant operator. -/
theorem symbol_saintVenant_apply (ξ : Vec d) (M : Fin d × Fin d → ℝ) (i j k l : Fin d) :
    ((∑ α ∈ Finset.Nat.antidiagonalTuple d 2, (∏ m, ξ m ^ α m) • saintVenant α) *ᵥ M)
        (i, j, k, l) =
      ξ j * ξ l * M (i, k) + ξ i * ξ k * M (j, l) - ξ i * ξ l * M (j, k) -
        ξ j * ξ k * M (i, l) := by
  rw [sum_symbol_saintVenant, Matrix.sum_mulVec]
  have : ∀ a b, ((ξ a * ξ b) • saintVenantT a b) *ᵥ M = saintVenantT a b *ᵥ ((ξ a * ξ b) • M) := by
    intro a b
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  simp only [Matrix.sum_mulVec, this]
  rw [sum_saintVenantT_mulVec (fun a b => (ξ a * ξ b) • M)]
  simp only [Pi.smul_apply, smul_eq_mul]

theorem sum_mul_self_of_norm_one {ξ : Vec d} (hξ : vecEuclideanNorm ξ = 1) :
    ∑ p, ξ p * ξ p = 1 := by
  have h : vecNormSq ξ = 1 := by
    have := Real.sqrt_eq_one.1 hξ
    exact this
  simpa [vecNormSq, vecDot] using h

/-- Contracting the equation `𝔸₂(ξ) M = 0` with `ξ_j ξ_l`. -/
theorem eq_of_contracted {ξ : Vec d} (hs : ∑ p, ξ p * ξ p = 1) {M : Fin d × Fin d → ℝ}
    (hM : ∀ p q, M (p, q) = M (q, p)) (i k : Fin d)
    (h : ∀ j l, ξ j * ξ l * M (i, k) + ξ i * ξ k * M (j, l) - ξ i * ξ l * M (j, k) -
      ξ j * ξ k * M (i, l) = 0) :
    M (i, k) = ξ i * (∑ j, M (k, j) * ξ j) + (∑ j, M (i, j) * ξ j) * ξ k -
      (∑ j, ∑ l, ξ j * ξ l * M (j, l)) * (ξ i * ξ k) := by
  have h0 : ∑ j, ∑ l, ξ j * ξ l * (ξ j * ξ l * M (i, k) + ξ i * ξ k * M (j, l) -
      ξ i * ξ l * M (j, k) - ξ j * ξ k * M (i, l)) = 0 :=
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => by rw [h j l, mul_zero]
  have t1 : ∑ j, ∑ l, ξ j * ξ l * (ξ j * ξ l * M (i, k)) = M (i, k) := by
    have : ∀ j l, ξ j * ξ l * (ξ j * ξ l * M (i, k)) =
        (ξ j * ξ j) * (ξ l * ξ l) * M (i, k) := fun j l => by ring
    simp only [this, ← Finset.sum_mul, ← Finset.mul_sum, hs]; ring
  have t2 : ∑ j, ∑ l, ξ j * ξ l * (ξ i * ξ k * M (j, l)) =
      (ξ i * ξ k) * ∑ j, ∑ l, ξ j * ξ l * M (j, l) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; ring
  have t3 : ∑ j, ∑ l, ξ j * ξ l * (ξ i * ξ l * M (j, k)) = ξ i * ∑ j, M (k, j) * ξ j := by
    have : ∀ j l, ξ j * ξ l * (ξ i * ξ l * M (j, k)) =
        (ξ l * ξ l) * (ξ i * (M (k, j) * ξ j)) := fun j l => by rw [hM j k]; ring
    simp only [this, ← Finset.sum_mul, ← Finset.mul_sum, hs]; ring
  have t4 : ∑ j, ∑ l, ξ j * ξ l * (ξ j * ξ k * M (i, l)) = (∑ j, M (i, j) * ξ j) * ξ k := by
    have : ∀ j l, ξ j * ξ l * (ξ j * ξ k * M (i, l)) =
        (ξ j * ξ j) * (M (i, l) * ξ l * ξ k) := fun j l => by ring
    simp only [this, ← Finset.sum_mul, ← Finset.mul_sum, hs]; ring
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at h0
  rw [t1, t2, t3, t4] at h0
  linarith

/-- For symmetric `M` and `|ξ| = 1`: `𝔸₂(ξ) M = 0` iff `M = a ⊗ ξ + ξ ⊗ a` for some
`a` (the necessary `a = Mξ - ½(ξ·Mξ)ξ` is explicit in the proof). -/
theorem symbol_saintVenant_mulVec_eq_zero_iff {M : Fin d × Fin d → ℝ}
    (hM : ∀ p q, M (p, q) = M (q, p)) {ξ : Vec d} (hξ : vecEuclideanNorm ξ = 1) :
    (∑ α ∈ Finset.Nat.antidiagonalTuple d 2, (∏ m, ξ m ^ α m) • saintVenant α) *ᵥ M = 0 ↔
      ∃ a : Vec d, ∀ p q, M (p, q) = a p * ξ q + ξ p * a q := by
  have hs := sum_mul_self_of_norm_one hξ
  constructor
  · intro h
    have hc : ∀ i j k l, ξ j * ξ l * M (i, k) + ξ i * ξ k * M (j, l) - ξ i * ξ l * M (j, k) -
        ξ j * ξ k * M (i, l) = 0 := fun i j k l => by
      rw [← symbol_saintVenant_apply, h]; rfl
    refine ⟨fun p => (∑ j, M (p, j) * ξ j) -
      (∑ j, ∑ l, ξ j * ξ l * M (j, l)) / 2 * ξ p, fun p q => ?_⟩
    rw [eq_of_contracted hs hM p q (fun j l => hc p j q l)]
    ring
  · rintro ⟨a, ha⟩
    funext r
    obtain ⟨i, j, k, l⟩ := r
    rw [symbol_saintVenant_apply, ha i k, ha j l, ha j k, ha i l]
    simp only [Pi.zero_apply]
    ring

/-- A nonzero symmetric `M` in the wave cone of the Saint-Venant operator
is `M_{pq} = (a'_p b_q + b_p a'_q)/2` with `a', b ≠ 0`. -/
theorem exists_symmTensor_of_mem_waveCone_saintVenant {M : Fin d × Fin d → ℝ}
    (hM : ∀ p q, M (p, q) = M (q, p)) (hM0 : M ≠ 0) (hmem : M ∈ waveCone 2 saintVenant) :
    ∃ a : Vec d, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
      M = fun p => (a p.1 * b p.2 + b p.1 * a p.2) / 2 := by
  obtain ⟨ξ, hξ, hker⟩ := hmem
  obtain ⟨a, ha⟩ := (symbol_saintVenant_mulVec_eq_zero_iff hM hξ).1 hker
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    simp [vecEuclideanNorm, vecNormSq, vecDot] at hξ
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hM0
    funext p
    simp [ha p.1 p.2]
  refine ⟨(2 : ℝ) • a, smul_ne_zero two_ne_zero ha0, ξ, hξ0, funext fun p => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ha p.1 p.2]
  ring

end AFree
