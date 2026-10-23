module

public import AFree.Curves.Defs

/-!
# Euclidean vector calculus helpers for curves

Bilinearity of `vecDot`, continuity, the orthogonal decomposition `v = (v ⬝ e) e + v_W`.
-/

@[expose] public section

namespace AFree.Curves

open PDE

variable {d : ℕ}

lemma vecDot_add_left (x y z : Vec d) : vecDot (x + y) z = vecDot x z + vecDot y z := by
  simp [vecDot, add_mul, Finset.sum_add_distrib]

lemma vecDot_sub_left (x y z : Vec d) : vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

lemma vecDot_smul_left (c : ℝ) (x y : Vec d) : vecDot (c • x) y = c * vecDot x y := by
  simp [vecDot, Finset.mul_sum, mul_assoc]

lemma vecDot_smul_right (c : ℝ) (x y : Vec d) : vecDot x (c • y) = c * vecDot x y := by
  rw [vecDot_comm, vecDot_smul_left, vecDot_comm]

lemma vecDot_sub_right (x y z : Vec d) : vecDot x (y - z) = vecDot x y - vecDot x z := by
  rw [vecDot_comm, vecDot_sub_left, vecDot_comm y, vecDot_comm z]

lemma vecDot_self (x : Vec d) : vecDot x x = vecNormSq x := rfl

lemma vecDot_zero_left (x : Vec d) : vecDot 0 x = 0 := by simp [vecDot]

lemma continuous_vecDot_left (y : Vec d) : Continuous fun x : Vec d => vecDot x y := by
  unfold vecDot; fun_prop

lemma continuous_vecNormSq : Continuous fun x : Vec d => vecNormSq x := by
  unfold vecNormSq vecDot; fun_prop

lemma continuous_vecEuclideanNorm : Continuous fun x : Vec d => vecEuclideanNorm x :=
  Real.continuous_sqrt.comp continuous_vecNormSq

lemma vecEuclideanNorm_sub_le (x y : Vec d) :
    vecEuclideanNorm (x - y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  have := vecEuclideanNorm_add_le x (-y)
  rwa [vecEuclideanNorm_neg, ← sub_eq_add_neg] at this

lemma vecEuclideanNorm_le_of_sq {x : Vec d} {r : ℝ} (hr : 0 ≤ r) (h : vecNormSq x ≤ r ^ 2) :
    vecEuclideanNorm x ≤ r := by
  unfold vecEuclideanNorm
  calc Real.sqrt (vecNormSq x) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt h
    _ = r := Real.sqrt_sq hr

/-- Pythagoras for the decomposition `v = (v ⬝ e) e + v_W` with `|e| = 1`. -/
lemma vecNormSq_sub_dot_smul {e : Vec d} (he : vecEuclideanNorm e = 1) (v : Vec d) :
    vecNormSq (v - vecDot v e • e) = vecNormSq v - vecDot v e ^ 2 := by
  have he2 : vecNormSq e = 1 := by
    have := vecEuclideanNorm_sq e; rw [he] at this; linarith
  have : vecNormSq (v - vecDot v e • e) =
      vecDot (v - vecDot v e • e) (v - vecDot v e • e) := rfl
  rw [this, vecDot_sub_left, vecDot_sub_right, vecDot_sub_right, vecDot_smul_left,
    vecDot_smul_right, vecDot_smul_left, vecDot_smul_right, vecDot_self, vecDot_self, he2,
    vecDot_comm e v]
  unfold vecNormSq; ring

lemma vecDot_sub_dot_smul {e : Vec d} (he : vecEuclideanNorm e = 1) (v : Vec d) :
    vecDot (v - vecDot v e • e) e = 0 := by
  have he2 : vecNormSq e = 1 := by
    have := vecEuclideanNorm_sq e; rw [he] at this; linarith
  rw [vecDot_sub_left, vecDot_smul_left, vecDot_self, he2]; ring

end AFree.Curves
