module

public import AFree.Defs
public import AFree.Proofs.BDProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Theorem 1.7]: for `u ∈ BD(Ω)`, at `|Eˢu|`-almost every point the polar of `Eˢu` is
`a ⊙ b = (a ⊗ b + b ⊗ a)/2` with `a ≠ 0` and `b ≠ 0`. -/
theorem polar_lebesgueSingularPart_eq_symmTensor {d : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (u : Vec d → Vec d) (Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ))
    (hEu : IsBDGradientOn Ω u Eu) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      ∃ a : Vec d, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Eu) x = fun p => (a p.1 * b p.2 + b p.1 * a p.2) / 2 := by exact AFree.BDProof.result Ω hΩ u Eu hEu

end AFree
