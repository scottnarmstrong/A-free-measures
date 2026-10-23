module

public import AFree.Defs
public import AFree.Rademacher.Dot
public import PDEFoundation.Ambient.Basis
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear algebra of the projection field `P`

Helper facts for the continuous frame construction: the data `P` of `IsBorelSubspaceField`, the orthogonal complement
`V(x)^⊥`, and `V(x)^⊥ = range (Id - P(x)) = ker P(x)`.
-/

@[expose] public section

open PDE Matrix

namespace AFree.Rademacher

variable {d : ℕ}

/-- The orthogonal complement `W^⊥ = {u | u · w = 0 for all w ∈ W}` of a subspace of `ℝ^d` for the
Euclidean dot product. -/
def vperp (W : Submodule ℝ (Vec d)) : Submodule ℝ (Vec d) where
  carrier := {u | ∀ w ∈ W, vecDot u w = 0}
  zero_mem' := fun w _ => vecDot_zero_left w
  add_mem' := fun {a b} ha hb w hw => by rw [vecDot_add_left, ha w hw, hb w hw, add_zero]
  smul_mem' := fun c a ha w hw => by rw [vecDot_smul_left, ha w hw, mul_zero]

/-- The witness form of `IsBorelSubspaceField`: `P x` is the (symmetric, idempotent) matrix of the
orthogonal projection onto `V x`, with Borel entries. -/
def IsBorelProj (V : Vec d → Submodule ℝ (Vec d)) (P : Vec d → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i j, Measurable fun x => P x i j) ∧
    ∀ x, (P x).transpose = P x ∧ P x * P x = P x ∧ LinearMap.range (Matrix.toLin' (P x)) = V x

theorem isBorelSubspaceField_iff {V : Vec d → Submodule ℝ (Vec d)} :
    IsBorelSubspaceField V ↔ ∃ P, IsBorelProj V P := Iff.rfl

theorem vecDot_mulVec {A : Matrix (Fin d) (Fin d) ℝ} (x y : Vec d) :
    vecDot x (A *ᵥ y) = vecDot (A.transpose *ᵥ x) y := by
  simp only [vecDot_eq_dotProduct, dotProduct_mulVec, mulVec_transpose]

variable {P : Matrix (Fin d) (Fin d) ℝ}

theorem vecDot_mulVec_symm (hP : P.transpose = P) (x y : Vec d) :
    vecDot x (P *ᵥ y) = vecDot (P *ᵥ x) y := by
  rw [vecDot_mulVec, hP]

/-- `u ⊥ V` iff `P u = 0`, for the projection matrix `P` of `V`. -/
theorem mem_vperp_iff_mulVec_eq_zero {W : Submodule ℝ (Vec d)} (hT : P.transpose = P)
    (hI : P * P = P) (hR : LinearMap.range (Matrix.toLin' P) = W) (u : Vec d) :
    u ∈ vperp W ↔ P *ᵥ u = 0 := by
  constructor
  · intro hu
    have hPu : P *ᵥ u ∈ W := hR ▸ ⟨u, by simp⟩
    have h1 := hu _ hPu
    have h2 : vecDot (P *ᵥ u) (P *ᵥ u) = vecDot u (P *ᵥ u) := by
      rw [← vecDot_mulVec_symm hT, mulVec_mulVec, hI]
    rw [h1, vecDot_self] at h2
    have : vecEuclideanNorm (P *ᵥ u) = 0 := by nlinarith [vecEuclideanNorm_nonneg (P *ᵥ u)]
    exact vecEuclideanNorm_eq_zero_iff.1 this
  · intro hu w hw
    rw [← hR] at hw
    obtain ⟨z, rfl⟩ := hw
    simp only [Matrix.toLin'_apply]
    rw [vecDot_mulVec_symm hT, hu, vecDot_zero_left]

theorem range_one_sub_eq_vperp {W : Submodule ℝ (Vec d)} (hT : P.transpose = P) (hI : P * P = P)
    (hR : LinearMap.range (Matrix.toLin' P) = W) :
    LinearMap.range (Matrix.toLin' (1 - P)) = vperp W := by
  ext u
  rw [mem_vperp_iff_mulVec_eq_zero hT hI hR]
  constructor
  · rintro ⟨z, rfl⟩
    simp only [Matrix.toLin'_apply]
    rw [mulVec_mulVec, mul_sub, mul_one, hI, sub_self, zero_mulVec]
  · intro hu
    refine ⟨u, ?_⟩
    simp only [Matrix.toLin'_apply, sub_mulVec, one_mulVec, hu, sub_zero]

theorem rank_one_sub_eq_finrank {W : Submodule ℝ (Vec d)} (hT : P.transpose = P) (hI : P * P = P)
    (hR : LinearMap.range (Matrix.toLin' P) = W) :
    (1 - P).rank = Module.finrank ℝ (vperp W) := by
  rw [← range_one_sub_eq_vperp hT hI hR]
  rfl

theorem col_one_sub_mem_vperp {W : Submodule ℝ (Vec d)} (hT : P.transpose = P) (hI : P * P = P)
    (hR : LinearMap.range (Matrix.toLin' P) = W) (a : Fin d) : (1 - P).col a ∈ vperp W := by
  rw [← range_one_sub_eq_vperp hT hI hR]
  refine ⟨basisVec a, ?_⟩
  rw [Matrix.toLin'_apply]
  exact mulVec_single_one _ a

/-- Entries of a symmetric idempotent real matrix are bounded by `1`. -/
theorem abs_entry_le_one (hT : P.transpose = P) (hI : P * P = P) (a b : Fin d) : |P a b| ≤ 1 := by
  have hdiag : ∀ a, P a a = ∑ k, P a k ^ 2 := by
    intro a
    have := congrFun (congrFun hI a) a
    rw [Matrix.mul_apply] at this
    conv_lhs => rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs : P k a = P a k := by
      have := congrFun (congrFun hT a) k
      simpa using this
    rw [hs]; ring
  have h1 : P a b ^ 2 ≤ P a a := by
    rw [hdiag a]
    exact Finset.single_le_sum (f := fun k => P a k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ b)
  have h2 : P a a ≤ 1 := by
    have h3 : P a a ^ 2 ≤ P a a := by
      calc P a a ^ 2 ≤ ∑ k, P a k ^ 2 :=
            Finset.single_le_sum (f := fun k => P a k ^ 2) (fun k _ => sq_nonneg _)
              (Finset.mem_univ a)
        _ = P a a := (hdiag a).symm
    have h4 : 0 ≤ P a a := by rw [hdiag a]; exact Finset.sum_nonneg fun k _ => sq_nonneg _
    nlinarith
  have : P a b ^ 2 ≤ 1 := h1.trans h2
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)

end AFree.Rademacher
