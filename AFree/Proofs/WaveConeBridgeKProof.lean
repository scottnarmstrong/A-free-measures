module

public import AFree.Paper.WaveConeK

/-!
# The wave cone via the complex symbol, order `k`

`P` lies in the wave cone iff the complex symbol `(2πi)^k Σ ξ^α A_α` annihilates it for some unit `ξ`.
-/

@[expose] public section

open Matrix PDE

namespace AFree.WaveConeBridgeKProof

/-- Equivalence of the real and complex-symbol descriptions of the wave cone of order `k`. -/
theorem result {ι κ : Type*} [Fintype ι] [Fintype κ] {d k : ℕ}
    (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P : ι → ℝ) :
    P ∈ waveCone k A ↔ ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧
      ((2 * Real.pi * Complex.I) ^ k •
          ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
            ((∏ i, ξ i ^ α i : ℝ) : ℂ) • (A α).map (fun a => (a : ℂ))) *ᵥ
        (fun i => (P i : ℂ)) = 0 :=
  waveCone_iff_complexSymbol A P

end AFree.WaveConeBridgeKProof
