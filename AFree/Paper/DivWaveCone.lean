module

public import AFree.Analysis.WaveCone
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The divergence operator and its wave cone

`(Div μ)_k = Σ_j ∂_j μ_{kj}` as a first-order operator on `ℝ^{d×d}`-valued measures; its wave
cone is the set of matrices of rank at most `d - 1` (proof of [DPR, Corollary 1.13]).
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- The coefficients of `Div`: `(Div μ)_k = Σ_j ∂_j μ_{kj}`, i.e.
`A_ℓ` sends `P` to the vector `k ↦ P (k, ℓ)`. -/
def divCoeff (d : ℕ) : Fin d → Matrix (Fin d) (Fin d × Fin d) ℝ :=
  fun ℓ k p => if p.1 = k ∧ p.2 = ℓ then 1 else 0

/-- The symbol of `Div`. -/
theorem divCoeff_symbol_mulVec {d : ℕ} (ξ : Vec d) (P : Fin d × Fin d → ℝ) :
    (∑ ℓ, ξ ℓ • divCoeff d ℓ) *ᵥ P = fun k => ∑ j, P (k, j) * ξ j := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    divCoeff, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

/-- For `d > 0`, `P` lies in the wave cone of `Div` iff the `d × d` matrix
`(P_{kj})` has rank at most `d - 1`. -/
theorem mem_waveConeFirstOrder_divCoeff_iff {d : ℕ} (hd : 0 < d) (P : Fin d × Fin d → ℝ) :
    P ∈ waveConeFirstOrder (divCoeff d) ↔ (Matrix.of fun k j => P (k, j)).rank ≤ d - 1 := by
  rw [mem_waveConeFirstOrder_iff_exists_ne_zero]
  set M : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun k j => P (k, j) with hM
  have hmv : ∀ ξ : Vec d, (∑ ℓ, ξ ℓ • divCoeff d ℓ) *ᵥ P = M *ᵥ ξ := by
    intro ξ
    rw [divCoeff_symbol_mulVec]
    rfl
  simp only [hmv]
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hrank : M.rank = Module.finrank ℝ (LinearMap.range M.mulVecLin) := rfl
  constructor
  · rintro ⟨ξ, hξ, h⟩
    have hne : LinearMap.ker M.mulVecLin ≠ ⊥ := by
      intro hb
      have hmem : ξ ∈ LinearMap.ker M.mulVecLin := LinearMap.mem_ker.2 h
      rw [hb] at hmem
      exact hξ (Submodule.mem_bot ℝ |>.1 hmem)
    have := Submodule.one_le_finrank_iff.2 hne
    omega
  · intro h
    have h1 : 1 ≤ Module.finrank ℝ (LinearMap.ker M.mulVecLin) := by omega
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.1 h1)
    exact ⟨ξ, hξ0, hξ⟩

end AFree
