module

public import AFree.Defs
public import AFree.Paper.OrderK.Rhs

/-!
# Proof of [DPR, Remark 1.3]

The augmented measure `(μ, σ)` is free for the augmented operator, so the main theorem applies.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree.MeasureRhsProof

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [DPR, Remark 1.3]: the conclusion of the main theorem holds if `𝒜μ = σ` for a measure `σ`. -/
theorem result {d k : ℕ} (hk : 1 ≤ k) (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (σ : VectorMeasure (Vec d) (κ → ℝ)) (hσ : euclideanVariation σ Ωᶜ = 0)
    (hrhs : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
      ∑ h ∈ Finset.range (k + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        (-1 : ℝ) ^ h • (A α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•μ) = ∫ᵛ x, φ x ∂•σ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveCone k A :=
  thm_rhs hk Ω hΩ A μ hμ σ hσ hrhs

end AFree.MeasureRhsProof
