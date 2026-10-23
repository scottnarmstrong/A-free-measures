module

public import AFree.Defs
public import AFree.Proofs.WaveConeBridgeProof
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- The wave cone `waveConeFirstOrder A` is the paper's `Λ_𝒜 = ⋃_{|ξ|=1} ker 𝔸¹(ξ)`, with the
symbol `𝔸¹(ξ) = 2πi Σ_ℓ ξ_ℓ A_ℓ` ([DPR, Section 2.1]). -/
theorem mem_waveConeFirstOrder_iff_complexSymbol {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Fin d → Matrix κ ι ℝ) (P : ι → ℝ) :
    P ∈ waveConeFirstOrder A ↔
      ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧
        ((2 * Real.pi * Complex.I) • ∑ ℓ, (ξ ℓ : ℂ) • (A ℓ).map (fun a => (a : ℂ))) *ᵥ
          (fun i => (P i : ℂ)) = 0 := by exact AFree.WaveConeBridgeProof.result A P

end AFree
