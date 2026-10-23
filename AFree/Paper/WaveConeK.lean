module

public import AFree.Defs
public import Mathlib.Analysis.Complex.Basic

/-!
# The order-`k` wave-cone bridge

The complex symbol `(2πi)^k Σ ξ^α A_α` applied to a real vector vanishes iff the real symbol does,
because `(2πi)^k ≠ 0` and the inclusion `ℝ → ℂ` is an injective ring homomorphism.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- `P ∈ Λ^{(k)}_𝒜` iff the paper's complex symbol `(2πi)^k Σ ξ^α A_α` kills `P`
for some unit `ξ`. -/
theorem waveCone_iff_complexSymbol {ι κ : Type*} [Fintype ι] [Fintype κ] {d k : ℕ} (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P : ι → ℝ) :
    P ∈ waveCone k A ↔ ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧
      ((2 * Real.pi * Complex.I) ^ k •
          ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
            ((∏ i, ξ i ^ α i : ℝ) : ℂ) • (A α).map (fun a => (a : ℂ))) *ᵥ
        (fun i => (P i : ℂ)) = 0 := by
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ^ k ≠ 0 :=
    pow_ne_zero _ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
  have key : ∀ ξ : Vec d,
      ((2 * Real.pi * Complex.I) ^ k •
          ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
            ((∏ i, ξ i ^ α i : ℝ) : ℂ) • (A α).map (fun a => (a : ℂ))) *ᵥ
        (fun i => (P i : ℂ)) = 0 ↔
        (∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • A α) *ᵥ P = 0 := by
    intro ξ
    have hM : (∑ α ∈ Finset.Nat.antidiagonalTuple d k,
        ((∏ i, ξ i ^ α i : ℝ) : ℂ) • (A α).map (fun a => (a : ℂ))) =
        (∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • A α).map
          (fun a => (a : ℂ)) := by
      ext i j
      simp [Matrix.sum_apply]
    have hv : (∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • A α).map
        (fun a => (a : ℂ)) *ᵥ (fun i => (P i : ℂ)) =
        fun r => ((((∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • A α) *ᵥ P) r : ℝ) : ℂ) := by
      funext r
      exact (RingHom.map_mulVec Complex.ofRealHom _ P r).symm
    rw [Matrix.smul_mulVec, hM, hv]
    constructor
    · intro h
      funext r
      have := congrFun h r
      simpa [h2] using this
    · intro h
      funext r
      simp [h]
  constructor
  · rintro ⟨ξ, h1, h2'⟩
    exact ⟨ξ, h1, (key ξ).2 h2'⟩
  · rintro ⟨ξ, h1, h2'⟩
    exact ⟨ξ, h1, (key ξ).1 h2'⟩

end AFree
