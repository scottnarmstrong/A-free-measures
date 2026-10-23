module

public import AFree.Defs
public import AFree.Paper.FreePair
public import AFree.Paper.Reindex

/-!
# Proof of [DPR, Theorem 1.1] for first-order operators

The `𝒜`-free vector measure `μ` gives the `𝒜`-free pair `(|μ|, polar μ)`, to which the pair version
of the main theorem applies.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree.FirstOrderMainProof

open PDE

/-- [DPR, Theorem 1.1] for `𝒜` of order at most one: `polar μ ∈ Λ_𝒜` at `|μ|^s`-a.e. point. -/
theorem result {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : Fin d → Matrix κ ι ℝ) (A₀ : Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFirstOrderFree Ω A A₀ μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveConeFirstOrder A :=
  ae_mem_waveCone_of_isFreePair' hΩ (euclideanVariation μ) (measurable_polar μ)
    (integrable_polar μ) (isFreePair_of_isFirstOrderFree hμ hfree)

end AFree.FirstOrderMainProof
