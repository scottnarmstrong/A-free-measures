module

public import AFree.Defs
public import AFree.Proofs.VariableCoeffProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [DPR, Remark 1.4]: Theorem 1.1 for operators with smooth variable coefficients `A_α(x)`,
`|α| ≤ k`, with, at `x`, the wave cone of the operator `Σ_{|α| ≤ k} A_α(x) ∂^α` with coefficients fixed at `x`. -/
theorem polar_mem_waveCone_var {d k : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ)
    (hA : ∀ α : Fin d → ℕ, ∑ i, α i ≤ k → ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x i j) Ω)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFreeVar Ω k A μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume,
      polar μ x ∈ waveCone k (fun α => A α x) := by exact AFree.VariableCoeffProof.result Ω hΩ A hA μ hμ hfree

end AFree
