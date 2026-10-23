module

public import AFree.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import AFree.Proofs.DivRankProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Corollary 1.13]: if `μ ∈ ℳ(Ω; ℝ^{d×d})` and `Div μ ∈ ℳ(Ω; ℝ^d)`, then the polar of `μ` has
rank at most `d - 1` at `|μ|ˢ`-almost every point. -/
theorem rank_polar_le_of_div_eq {d : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (μ : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (σ : VectorMeasure (Vec d) (Vec d)) (hσ : euclideanVariation σ Ωᶜ = 0)
    (hdiv : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∀ k,
      -∑ j, (∫ᵛ x, euclideanCoordDeriv j φ x ∂•μ) (k, j) = (∫ᵛ x, φ x ∂•σ) k) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume,
      (Matrix.of fun k j => polar μ x (k, j)).rank ≤ d - 1 := by exact AFree.DivRankProof.result Ω hΩ μ hμ σ hσ hdiv

end AFree
