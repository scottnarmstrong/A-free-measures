module

public import AFree.Defs
public import AFree.Paper.OrderK.Main

/-!
# Proof of [DPR, Theorem 1.1]

The `𝒜`-free measure `μ` gives the `𝒜`-free pair `(|μ|, polar μ)`, to which the pair version of the
main theorem applies.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree.GeneralMainProof

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [DPR, Theorem 1.1]: `polar μ ∈ Λ_𝒜` at `|μ|^s`-a.e. point for an `𝒜`-free measure `μ` of order `k`. -/
theorem result {d k : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFree Ω k A μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveCone k A :=
  thm_general Ω hΩ A μ hμ hfree

end AFree.GeneralMainProof
