module

public import AFree.Defs
public import AFree.Proofs.GeneralMainProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [DPR, Theorem 1.1]: if `𝒜μ = Σ_{|α| ≤ k} A_α ∂^α μ = 0` on an open set `Ω`, then the polar of `μ`
lies in the wave cone `Λ_𝒜` at `|μ|ˢ`-almost every point. -/
theorem polar_mem_waveCone {d k : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFree Ω k A μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveCone k A := by exact AFree.GeneralMainProof.result Ω hΩ A μ hμ hfree

end AFree
