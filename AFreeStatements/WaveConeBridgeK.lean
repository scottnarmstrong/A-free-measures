module

public import AFree.Defs
public import AFree.Proofs.WaveConeBridgeKProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The wave cone `waveCone k A` is the paper's `Λ_𝒜 = ⋃_{|ξ|=1} ker 𝔸^k(ξ)`, with the principal
symbol `𝔸^k(ξ) = (2πi)^k Σ_{|α|=k} ξ^α A_α` ([DPR, Section 2.1]). -/
theorem mem_waveCone_iff_complexSymbol {d k : ℕ} (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P : ι → ℝ) :
    P ∈ waveCone k A ↔ ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧
      ((2 * Real.pi * Complex.I) ^ k •
          ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
            ((∏ i, ξ i ^ α i : ℝ) : ℂ) • (A α).map (fun a => (a : ℂ))) *ᵥ
        (fun i => (P i : ℂ)) = 0 := by exact AFree.WaveConeBridgeKProof.result A P

end AFree
