module

public import AFree.Rademacher.Robust
public import AFree.Rademacher.Chain.Cut

/-!
# Basic calculus facts for the single-stage perturbation

Calculus helpers for the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE Filter Topology Set

namespace AFree.Rademacher

variable {d : ℕ}

theorem X0_iff_fderiv {e : Vec d → Fin d → Vec d} {f : Vec d → ℝ} :
    f ∈ X0 e ↔ ContDiff ℝ (⊤ : ℕ∞) f ∧ (∃ C : ℝ, ∀ x, |f x| ≤ C) ∧
      ∀ x j, |fderiv ℝ f x (e x j)| ≤ 1 := by
  simp only [X0, mem_ofPred_eq, vecDot_euclGrad]

theorem fderiv_add_const_mul {f g : Vec d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (c : ℝ) (x w : Vec d) :
    fderiv ℝ (fun y => f y + c * g y) x w = fderiv ℝ f x w + c * fderiv ℝ g x w := by
  rw [fderiv_fun_add (hf x) ((hg x).const_mul c), fderiv_const_mul (hg x)]
  simp

theorem vecDot_proj_orth {n : Vec d} (hn : vecEuclideanNorm n = 1) (u : Vec d) :
    vecDot (u - vecDot u n • n) n = 0 := by
  rw [vecDot_sub_left, vecDot_smul_left, vecDot_self, hn]
  ring

theorem vecEuclideanNorm_proj_orth_le {n : Vec d} (hn : vecEuclideanNorm n = 1) (u : Vec d) :
    vecEuclideanNorm (u - vecDot u n • n) ≤ vecEuclideanNorm u := by
  have hnn : vecDot n n = 1 := by rw [vecDot_self, hn]; ring
  have h : vecDot (u - vecDot u n • n) (u - vecDot u n • n) =
      vecDot u u - vecDot u n ^ 2 := by
    rw [vecDot_sub_left, vecDot_sub_right, vecDot_sub_right, vecDot_smul_left, vecDot_smul_right,
      vecDot_smul_left, vecDot_smul_right, hnn, vecDot_comm n u]
    ring
  rw [vecDot_self, vecDot_self] at h
  have h2 : vecEuclideanNorm (u - vecDot u n • n) ^ 2 ≤ vecEuclideanNorm u ^ 2 := by
    rw [h]; nlinarith [sq_nonneg (vecDot u n)]
  exact (pow_le_pow_iff_left₀ (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_nonneg _)
    two_ne_zero).1 h2

/-- A gradient bound for `g` from a bound on the derivative along `n` and on the derivative along
`n^⊥`. -/
theorem abs_fderiv_le_of_normal {g : Vec d → ℝ} {x : Vec d} {n : Vec d}
    (hn : vecEuclideanNorm n = 1) {A W : ℝ} (hA : |fderiv ℝ g x n| ≤ A) (hW0 : 0 ≤ W)
    (hW : ∀ w, vecDot w n = 0 → |fderiv ℝ g x w| ≤ W * vecEuclideanNorm w) (u : Vec d) :
    |fderiv ℝ g x u| ≤ (A + W) * vecEuclideanNorm u := by
  have hu : u = vecDot u n • n + (u - vecDot u n • n) := by abel
  have h1 : |vecDot u n| ≤ vecEuclideanNorm u := by
    have := abs_vecDot_le_vecEuclideanNorm_mul u n
    rwa [hn, mul_one] at this
  have h2 := hW _ (vecDot_proj_orth hn u)
  have h3 := vecEuclideanNorm_proj_orth_le hn u
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  calc |fderiv ℝ g x u|
      = |vecDot u n * fderiv ℝ g x n + fderiv ℝ g x (u - vecDot u n • n)| := by
        conv_lhs => rw [hu]
        rw [map_add, map_smul, smul_eq_mul]
    _ ≤ |vecDot u n| * |fderiv ℝ g x n| + |fderiv ℝ g x (u - vecDot u n • n)| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ vecEuclideanNorm u * A + W * vecEuclideanNorm u := by
        refine add_le_add (mul_le_mul h1 hA (abs_nonneg _) (vecEuclideanNorm_nonneg _)) ?_
        exact h2.trans (mul_le_mul_of_nonneg_left h3 hW0)
    _ = _ := by ring

end AFree.Rademacher
