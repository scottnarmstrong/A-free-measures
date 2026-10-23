module

public import AFree.Defs
public import Mathlib.Analysis.Complex.Basic

/-!
# The wave cone via the complex symbol, order one

The complex symbol `2πi Σ_ℓ ξ_ℓ A_ℓ` applied to a real vector vanishes iff the real symbol does,
because `2πi ≠ 0`.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree.WaveConeBridgeProof

open PDE

/-- Equivalence of the real and complex-symbol descriptions of the first-order wave cone. -/
theorem result {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Fin d → Matrix κ ι ℝ) (P : ι → ℝ) :
    P ∈ waveConeFirstOrder A ↔
      ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧
        ((2 * Real.pi * Complex.I) • ∑ ℓ, (ξ ℓ : ℂ) • (A ℓ).map (fun a => (a : ℂ))) *ᵥ
          (fun i => (P i : ℂ)) = 0 := by
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ ξ : Vec d,
      ((2 * Real.pi * Complex.I) • ∑ ℓ, (ξ ℓ : ℂ) • (A ℓ).map (fun a => (a : ℂ))) *ᵥ
        (fun i => (P i : ℂ)) = 0 ↔ (∑ ℓ, ξ ℓ • A ℓ) *ᵥ P = 0 := by
    intro ξ
    have hM : (∑ ℓ, (ξ ℓ : ℂ) • (A ℓ).map (fun a => (a : ℂ))) =
        (∑ ℓ, ξ ℓ • A ℓ).map (fun a => (a : ℂ)) := by
      ext i j
      simp [Matrix.sum_apply]
    have hv : (∑ ℓ, ξ ℓ • A ℓ).map (fun a => (a : ℂ)) *ᵥ (fun i => (P i : ℂ)) =
        fun k => (((∑ ℓ, ξ ℓ • A ℓ) *ᵥ P) k : ℂ) := by
      funext k
      have := RingHom.map_mulVec Complex.ofRealHom (∑ ℓ, ξ ℓ • A ℓ) P k
      exact this.symm
    rw [Matrix.smul_mulVec, hM, hv]
    constructor
    · intro h
      funext k
      have := congrFun h k
      simpa [h2] using this
    · intro h
      funext k
      simp [h]
  constructor
  · rintro ⟨ξ, h1, h2'⟩
    exact ⟨ξ, h1, (key ξ).2 h2'⟩
  · rintro ⟨ξ, h1, h2'⟩
    exact ⟨ξ, h1, (key ξ).1 h2'⟩

end AFree.WaveConeBridgeProof
