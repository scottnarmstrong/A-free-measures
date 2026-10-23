module

public import AFree.Curves.BundleTop.Fixed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Orthogonal projection matrices

`IsProj P W`: `P` is the matrix of the orthogonal projection onto `W`. Existence, uniqueness, and
`tr P = dim W`.
-/

@[expose] public section

open Set Matrix

namespace AFree.BundleTop

open PDE AFree.Curves

variable {d : ℕ}

/-- `P` is the matrix of the orthogonal projection onto `W`. -/
def IsProj (P : Matrix (Fin d) (Fin d) ℝ) (W : Submodule ℝ (Vec d)) : Prop :=
  Pᵀ = P ∧ P * P = P ∧ LinearMap.range (Matrix.toLin' P) = W

variable {P : Matrix (Fin d) (Fin d) ℝ} {W : Submodule ℝ (Vec d)}

lemma IsProj.mem_iff (h : IsProj P W) (y : Vec d) : y ∈ W ↔ P *ᵥ y = y := by
  rw [← h.2.2]
  constructor
  · rintro ⟨x, rfl⟩
    simp only [Matrix.toLin'_apply]
    rw [mulVec_mulVec, h.2.1]
  · intro hy
    exact ⟨y, by simpa using hy⟩

lemma IsProj.mulVec_mem (h : IsProj P W) (y : Vec d) : P *ᵥ y ∈ W := by
  rw [← h.2.2]; exact ⟨y, by simp⟩

/-- A symmetric idempotent matrix is determined by its range. -/
lemma IsProj.unique {P' : Matrix (Fin d) (Fin d) ℝ} (h : IsProj P W) (h' : IsProj P' W) :
    P = P' := by
  have h1 : P' * P = P := Matrix.ext_iff_mulVec.2 fun y => by
    rw [← mulVec_mulVec, (h'.mem_iff _).1 (h.mulVec_mem y)]
  have h2 : P * P' = P' := Matrix.ext_iff_mulVec.2 fun y => by
    rw [← mulVec_mulVec, (h.mem_iff _).1 (h'.mulVec_mem y)]
  have h3 : P' * P = P' := by
    have := congrArg Matrix.transpose h2
    rwa [transpose_mul, h.1, h'.1] at this
  rw [← h1, h3]

/-- `tr P = dim W`. -/
lemma IsProj.trace_eq (h : IsProj P W) : P.trace = (Module.finrank ℝ W : ℝ) := by
  have hidem : IsIdempotentElem (Matrix.toLin' P) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h.2.1]
  have h' := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [h.2.2] at h'
  rw [← h', Matrix.trace_toLin'_eq]

/-- Every subspace has an orthogonal projection matrix. -/
lemma exists_isProj (W : Submodule ℝ (Vec d)) : ∃ P, IsProj P W := by
  classical
  set b := Module.finBasis ℝ W with hb
  set k := Module.finrank ℝ W
  set B : Matrix (Fin d) (Fin k) ℝ := Matrix.of fun i j => (b j : Vec d) i with hB
  have hBz : ∀ z : Fin k → ℝ, B *ᵥ z = ∑ j, z j • (b j : Vec d) := by
    intro z; ext i
    simp [hB, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hBmem : ∀ z, B *ᵥ z ∈ W := fun z => by
    rw [hBz]; exact W.sum_mem fun j _ => W.smul_mem _ (b j).2
  have hBinj : Function.Injective B.mulVec := by
    intro z z' hzz
    have : B *ᵥ (z - z') = 0 := by rw [Matrix.mulVec_sub, hzz, sub_self]
    rw [hBz] at this
    have h2 : ∑ j, (z - z') j • b j = 0 := by
      apply Subtype.ext
      simpa using this
    have := Fintype.linearIndependent_iff.1 b.linearIndependent (z - z') h2
    ext j; have := this j; simp only [Pi.sub_apply] at this; linarith
  set G : Matrix (Fin k) (Fin k) ℝ := Bᵀ * B with hG
  have hGinj : Function.Injective G.mulVec := by
    intro z z' hzz
    have h0 : G *ᵥ (z - z') = 0 := by rw [Matrix.mulVec_sub, hzz, sub_self]
    have h1 : (B *ᵥ (z - z')) ⬝ᵥ (B *ᵥ (z - z')) = 0 := by
      have : (z - z') ⬝ᵥ (G *ᵥ (z - z')) = (B *ᵥ (z - z')) ⬝ᵥ (B *ᵥ (z - z')) := by
        rw [hG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      rw [← this, h0, dotProduct_zero]
    have h2 : B *ᵥ (z - z') = 0 := dotProduct_self_eq_zero.1 h1
    have : B *ᵥ z = B *ᵥ z' := by
      rw [Matrix.mulVec_sub] at h2; exact sub_eq_zero.1 h2
    exact hBinj this
  have hGu : IsUnit G.det :=
    (Matrix.isUnit_iff_isUnit_det G).1 ((Matrix.mulVec_injective_iff_isUnit).1 hGinj)
  have hGsymm : Gᵀ = G := by rw [hG, transpose_mul, transpose_transpose]
  have hGi : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGu
  refine ⟨B * G⁻¹ * Bᵀ, ?_, ?_, ?_⟩
  · rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.transpose_nonsing_inv, hGsymm,
      Matrix.mul_assoc]
  · calc B * G⁻¹ * Bᵀ * (B * G⁻¹ * Bᵀ) = B * (G⁻¹ * (Bᵀ * B) * G⁻¹) * Bᵀ := by
          simp only [Matrix.mul_assoc]
      _ = B * G⁻¹ * Bᵀ := by
          rw [← hG, hGi, Matrix.one_mul, Matrix.mul_assoc]
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      exact hBmem _
    · intro y hy
      obtain ⟨c, hc⟩ : ∃ c : Fin k → ℝ, B *ᵥ c = y := by
        refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
        rw [hBz]
        have h := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        exact h
      refine ⟨y, ?_⟩
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      rw [← hc, Matrix.mulVec_mulVec c Bᵀ B, ← hG, Matrix.mulVec_mulVec c G⁻¹ G, hGi,
        Matrix.one_mulVec]

end AFree.BundleTop
