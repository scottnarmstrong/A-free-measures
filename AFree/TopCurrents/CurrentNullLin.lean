module

public import AFree.TopCurrents.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Linear algebra for the vanishing of `ν` on null sets

An orthogonal matrix with last row `e`, and the Jacobian determinant of the tuple obtained from the
rows of this matrix by replacing the last one with a function `g`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE

/-- There is an orthogonal matrix whose last row is the unit vector `e`. -/
lemma exists_orthRows {n : ℕ} {e : Vec (n + 1)} (he : vecEuclideanNorm e = 1) :
    ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, R * R.transpose = 1 ∧
      ∀ j, R (Fin.last n) j = e j := by
  let E := PiLp 2 (fun _ : Fin (n + 1) => ℝ)
  let v : Fin (n + 1) → E := fun _ => WithLp.toLp 2 e
  have hsq : ∑ j, e j * e j = 1 := by
    have h1 : vecNormSq e = 1 := by
      have := vecEuclideanNorm_sq e
      rw [he] at this
      linarith
    simpa [vecNormSq, vecDot] using h1
  have hv : Orthonormal ℝ (({Fin.last n} : Set (Fin (n + 1))).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : Fin (n + 1)) = Fin.last n := i.2
    have hj : (j : Fin (n + 1)) = Fin.last n := j.2
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    subst hij
    simp only [Set.domRestrict_apply, v, ite_true]
    rw [PiLp.inner_apply]
    simpa [sq] using hsq
  have hcard : Module.finrank ℝ E = Fintype.card (Fin (n + 1)) := by simp [E]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  refine ⟨Matrix.of fun i j => b i j, ?_, fun j => ?_⟩
  · ext i k
    have := orthonormal_iff_ite.1 b.orthonormal i k
    rw [PiLp.inner_apply] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [show (∑ j, b i j * b k j) = ∑ j, inner ℝ (b i j) (b k j) by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [mul_comm]]
    rw [this]
  · have := hb (Fin.last n) rfl
    simp [this, v]

/-- The tuple `y ↦ ((R y)_i)_i` with the last component replaced by `g`. -/
noncomputable def rowTuple {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (g : Vec (n + 1) → ℝ) :
    Fin (n + 1) → Vec (n + 1) → ℝ :=
  Function.update (fun i y => ∑ j, R i j * y j) (Fin.last n) g

lemma rowTuple_ne {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (g : Vec (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : i ≠ Fin.last n) (y : Vec (n + 1)) :
    rowTuple R g i y = ∑ j, R i j * y j := by
  simp [rowTuple, Function.update_of_ne hi]

lemma rowTuple_last {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (g : Vec (n + 1) → ℝ) :
    rowTuple R g (Fin.last n) = g := by
  simp [rowTuple]

lemma fderiv_linRow {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (y : Vec (n + 1)) (j : Fin (n + 1)) :
    fderiv ℝ (fun y : Vec (n + 1) => ∑ j, R i j * y j) y (Pi.single j 1) = R i j := by
  have h : HasFDerivAt (fun y : Vec (n + 1) => ∑ j, R i j * y j)
      (∑ k, R i k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k) y := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (A := fun k (y : Vec (n + 1)) => R i k * y k)
      (A' := fun k => R i k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k)
      (x := y) fun k _ => ((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (n + 1) => ℝ) k).hasFDerivAt).const_mul (R i k)
    simpa using this
  rw [h.fderiv]
  simp [Pi.single_apply]

lemma linRow_eucl {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hR : R * R.transpose = 1)
    (i : Fin (n + 1)) :
    IsEuclLipschitzWith 1 (fun y : Vec (n + 1) => ∑ j, R i j * y j) := by
  intro x y
  have hrow : vecEuclideanNorm (fun j => R i j) = 1 := by
    have h := congrFun (congrFun hR i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, ite_true] at h
    unfold vecEuclideanNorm vecNormSq vecDot
    simp only
    rw [h, Real.sqrt_one]
  have : (∑ j, R i j * x j) - ∑ j, R i j * y j = vecDot (fun j => R i j) (x - y) := by
    simp [vecDot, mul_sub, Finset.sum_sub_distrib]
  rw [this]
  have h2 := abs_vecDot_le_vecEuclideanNorm_mul (fun j => R i j) (x - y)
  simpa [hrow] using h2

lemma det_sq_of_orth {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hR : R * R.transpose = 1) :
    R.det = 1 ∨ R.det = -1 := by
  have h := congrArg Matrix.det hR
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.1 h

/-- The Jacobian determinant of `rowTuple R g` is `det R · D_e g`. -/
lemma jacDet_rowTuple {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hR : R * R.transpose = 1)
    {e : Vec (n + 1)} (he : ∀ j, R (Fin.last n) j = e j) {g : Vec (n + 1) → ℝ}
    (y : Vec (n + 1)) :
    jacDet (rowTuple R g) y = R.det * fderiv ℝ g y e := by
  set w : Fin (n + 1) → ℝ := fun j => ∑ k, fderiv ℝ g y (Pi.single k 1) * R j k with hw
  have hRR : R.transpose * R = 1 := mul_eq_one_comm.1 hR
  have hJ : jacMat (rowTuple R g) y = (Matrix.updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      (Fin.last n) w) * R := by
    ext i j
    by_cases hi : i = Fin.last n
    · subst hi
      simp only [jacMat, Matrix.of_apply, rowTuple_last, Matrix.mul_apply,
        Matrix.updateRow_self, hw]
      have : ∀ k, fderiv ℝ g y (Pi.single k 1) = ∑ l, (∑ m, fderiv ℝ g y (Pi.single m 1) * R l m) * R l k := by
        intro k
        have h1 : ∀ m, ∑ l, R l m * R l k = if m = k then 1 else 0 := by
          intro m
          have := congrFun (congrFun hRR m) k
          simpa [Matrix.mul_apply, Matrix.one_apply] using this
        calc fderiv ℝ g y (Pi.single k 1)
            = ∑ m, fderiv ℝ g y (Pi.single m 1) * (if m = k then 1 else 0) := by simp
          _ = ∑ m, fderiv ℝ g y (Pi.single m 1) * ∑ l, R l m * R l k := by simp [h1]
          _ = _ := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
      rw [this j]
    · simp only [jacMat, Matrix.of_apply, Matrix.mul_apply, Matrix.updateRow_ne hi]
      rw [show rowTuple R g i = fun y => ∑ j, R i j * y j from funext (rowTuple_ne R g hi),
        fderiv_linRow]
      simp [Matrix.one_apply]
  have hM : (Matrix.updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (Fin.last n) w).det =
      w (Fin.last n) := by
    have := Matrix.det_updateRow_sum (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (Fin.last n) w
    have e1 : (∑ k, w k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) k) = w := by
      funext j
      simp [Matrix.one_apply]
    rw [e1] at this
    simpa using this
  have hwl : w (Fin.last n) = fderiv ℝ g y e := by
    have : e = ∑ k, e k • (Pi.single k 1 : Vec (n + 1)) := by
      funext j; simp [Pi.single_apply]
    conv_rhs => rw [this]
    simp only [map_sum, map_smul, smul_eq_mul, hw, he]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold jacDet
  rw [hJ, Matrix.det_mul, hM, hwl, mul_comm]

end AFree
