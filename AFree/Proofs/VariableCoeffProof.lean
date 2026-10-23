module

public import AFree.Defs
public import AFree.Paper.OrderK.Var

/-!
# Proof of [DPR, Remark 1.4]
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree.VariableCoeffProof

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [DPR, Remark 1.4]: the main theorem for variable `C^∞` coefficients, with the wave cone taken pointwise. -/
theorem result {d k : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ)
    (hA : ∀ α : Fin d → ℕ, ∑ i, α i ≤ k → ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x i j) Ω)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFreeVar Ω k A μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume,
      polar μ x ∈ waveCone k (fun α => A α x) :=
  thm_var Ω hΩ A hA μ hμ hfree

end AFree.VariableCoeffProof
