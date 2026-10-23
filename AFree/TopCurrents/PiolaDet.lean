module

public import AFree.TopCurrents.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Derivative of a determinant of differentiable rows

Auxiliary calculus for the Piola identity: the derivative of `y ↦ det (M a j y)` is the sum over rows `a`
of the determinants with row `a` replaced by its derivative.
-/

@[expose] public section

namespace AFree

open Matrix

/-- The determinant as a continuous multilinear map of the rows. -/
noncomputable def detCont (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ where
  toMultilinearMap := (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap
  cont := by
    show Continuous fun m : Fin n → Fin n → ℝ => (Matrix.of m).det
    exact (continuous_id.matrix_det : Continuous fun M : Matrix (Fin n) (Fin n) ℝ => M.det)

lemma detCont_apply {n : ℕ} (m : Fin n → Fin n → ℝ) : detCont n m = (Matrix.of m).det := rfl

/-- Derivative of a determinant of differentiable rows, applied to a vector. -/
theorem hasFDerivAt_det_rows {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {M : Fin n → Fin n → E → ℝ} {M' : Fin n → Fin n → E →L[ℝ] ℝ} {x : E}
    (h : ∀ a j, HasFDerivAt (M a j) (M' a j) x) :
    ∃ D : E →L[ℝ] ℝ, HasFDerivAt (fun y => (Matrix.of fun a j => M a j y).det) D x ∧
      ∀ v, D v = ∑ a, ((Matrix.of fun a j => M a j x).updateRow a (fun j => M' a j v)).det := by
  classical
  have hrow : ∀ a, HasFDerivAt (fun y => fun j => M a j y) (ContinuousLinearMap.pi (M' a)) x :=
    fun a => hasFDerivAt_pi'.2 (h a)
  have key := HasFDerivAt.multilinear_comp (f := detCont n) hrow
  refine ⟨_, key, fun v => ?_⟩
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  show detCont n (Function.update (fun b j => M b j x) a (fun j => M' a j v)) = _
  rw [detCont_apply]
  congr 2

end AFree
