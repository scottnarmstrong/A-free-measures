module

public import AFree.Proofs.FirstOrderMainProof
public import AFree.Paper.DivAssembly

@[expose] public section

open MeasureTheory Matrix

namespace AFree.DivRankProof

open PDE AFree

/-- [DPR, Corollary 1.13]: if `div μ` is a measure, the polar of `μ^s` has rank at most `d - 1`; this uses
[DPR, Remark 1.3] and [DPR, Theorem 1.1]. -/
theorem result {d : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (μ : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (σ : VectorMeasure (Vec d) (Vec d)) (hσ : euclideanVariation σ Ωᶜ = 0)
    (hdiv : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∀ k,
      -∑ j, (∫ᵛ x, euclideanCoordDeriv j φ x ∂•μ) (k, j) = (∫ᵛ x, φ x ∂•σ) k) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume,
      (Matrix.of fun k j => polar μ x (k, j)).rank ≤ d - 1 :=
  rank_polar_le_of_div_eq_of_main
    (fun Ω hΩ A A₀ μ hμ hfree => FirstOrderMainProof.result Ω hΩ A A₀ μ hμ hfree)
    Ω hΩ μ hμ σ hσ hdiv

end AFree.DivRankProof
