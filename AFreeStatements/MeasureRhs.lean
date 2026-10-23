module

public import AFree.Defs
public import AFree.Proofs.MeasureRhsProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [DPR, Remark 1.3]: the conclusion of Theorem 1.1 holds when `𝒜μ = σ` is a measure, for an
operator of order `k ≥ 1`. -/
theorem polar_mem_waveCone_of_eq_measure {d k : ℕ} (hk : 1 ≤ k) (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (σ : VectorMeasure (Vec d) (κ → ℝ)) (hσ : euclideanVariation σ Ωᶜ = 0)
    (hrhs : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
      ∑ h ∈ Finset.range (k + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        (-1 : ℝ) ^ h • (A α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•μ) = ∫ᵛ x, φ x ∂•σ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveCone k A := by exact AFree.MeasureRhsProof.result hk Ω hΩ A μ hμ σ hσ hrhs

end AFree
