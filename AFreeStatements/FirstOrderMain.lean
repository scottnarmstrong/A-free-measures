module

public import AFree.Defs
public import AFree.Proofs.FirstOrderMainProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Theorem 1.1] for operators of order at most one: if `Σ_ℓ A_ℓ ∂_ℓ μ + A₀ μ = 0` on an
open set `Ω`, then the polar of `μ` lies in the wave cone `Λ_𝒜` at `|μ|ˢ`-almost every point. -/
theorem polar_mem_waveConeFirstOrder {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : Fin d → Matrix κ ι ℝ) (A₀ : Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFirstOrderFree Ω A A₀ μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveConeFirstOrder A := by exact AFree.FirstOrderMainProof.result Ω hΩ A A₀ μ hμ hfree

end AFree
