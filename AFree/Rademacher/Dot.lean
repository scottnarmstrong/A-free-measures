module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Bilinearity of the Euclidean dot product on `Vec d`

Small helper lemmas for `PDE.vecDot`, via `Matrix.dotProduct`, used by the Rademacher files.
-/

@[expose] public section

open PDE

namespace AFree.Rademacher

variable {d : ℕ}

theorem vecDot_eq_dotProduct (x y : Vec d) : vecDot x y = x ⬝ᵥ y := rfl

theorem vecDot_add_left (x y z : Vec d) : vecDot (x + y) z = vecDot x z + vecDot y z := by
  simp only [vecDot_eq_dotProduct, add_dotProduct]

theorem vecDot_add_right (x y z : Vec d) : vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot_eq_dotProduct, dotProduct_add]

theorem vecDot_sub_left (x y z : Vec d) : vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot_eq_dotProduct, sub_dotProduct]

theorem vecDot_sub_right (x y z : Vec d) : vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp only [vecDot_eq_dotProduct, dotProduct_sub]

theorem vecDot_smul_left (c : ℝ) (x y : Vec d) : vecDot (c • x) y = c * vecDot x y := by
  simp only [vecDot_eq_dotProduct, smul_dotProduct, smul_eq_mul]

theorem vecDot_smul_right (c : ℝ) (x y : Vec d) : vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot_eq_dotProduct, dotProduct_smul, smul_eq_mul]

theorem vecDot_zero_left (y : Vec d) : vecDot 0 y = 0 := by simp [vecDot_eq_dotProduct]

theorem vecDot_zero_right (y : Vec d) : vecDot y 0 = 0 := by simp [vecDot_eq_dotProduct]

theorem vecDot_sum_left {ι : Type*} (s : Finset ι) (f : ι → Vec d) (y : Vec d) :
    vecDot (∑ i ∈ s, f i) y = ∑ i ∈ s, vecDot (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vecDot_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, vecDot_add_left, ih]

theorem vecDot_sum_right {ι : Type*} (s : Finset ι) (x : Vec d) (f : ι → Vec d) :
    vecDot x (∑ i ∈ s, f i) = ∑ i ∈ s, vecDot x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vecDot_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, vecDot_add_right, ih]

theorem vecDot_self (x : Vec d) : vecDot x x = vecEuclideanNorm x ^ 2 := by
  rw [vecEuclideanNorm_sq]; rfl

theorem continuous_vecDot : Continuous fun p : Vec d × Vec d => vecDot p.1 p.2 := by
  unfold vecDot
  fun_prop

theorem continuous_vecEuclideanNorm : Continuous fun x : Vec d => vecEuclideanNorm x := by
  have : Continuous fun x : Vec d => vecDot x x := continuous_vecDot.comp (continuous_id.prodMk continuous_id)
  exact Real.continuous_sqrt.comp this

theorem continuousOn_vecDot {α : Type*} [TopologicalSpace α] {f g : α → Vec d} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => vecDot (f x) (g x)) s :=
  continuous_vecDot.comp_continuousOn (hf.prodMk hg)

theorem continuousOn_vecEuclideanNorm {α : Type*} [TopologicalSpace α] {f : α → Vec d} {s : Set α}
    (hf : ContinuousOn f s) : ContinuousOn (fun x => vecEuclideanNorm (f x)) s :=
  continuous_vecEuclideanNorm.comp_continuousOn hf

/-- Completeness of an orthonormal `d`-tuple of `ℝ^d`: `∑ⱼ (g · eⱼ)² = |g|²`. -/
theorem sum_sq_vecDot_eq_vecNormSq {e : Fin d → Vec d}
    (he : ∀ k l, vecDot (e k) (e l) = if k = l then 1 else 0) (g : Vec d) :
    ∑ j, vecDot g (e j) ^ 2 = vecNormSq g := by
  classical
  let A : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun j a => e j a
  have h1 : A * A.transpose = 1 := by
    ext j k
    have := he j k
    simp only [vecDot, A, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.one_apply] at this ⊢
    exact this
  have h2 : A.transpose * A = 1 := mul_eq_one_comm.1 h1
  have h3 : ∀ a b, ∑ j, e j a * e j b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun h2 a) b
    simpa [Matrix.mul_apply, A, Matrix.one_apply] using this
  calc ∑ j, vecDot g (e j) ^ 2
      = ∑ j, ∑ a, ∑ b, g a * g b * (e j a * e j b) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [vecDot, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a, ∑ b, g a * g b * ∑ j, e j a * e j b := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
    _ = vecNormSq g := by
        simp only [h3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          vecNormSq, vecDot]

end AFree.Rademacher
