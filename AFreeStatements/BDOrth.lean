module

public import AFree.Defs
public import AFree.Proofs.BDOrthProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Corollary 1.8]: if moreover `div u ∈ L²(Ω)`, the vectors `a` and `b` can be taken with
`a · b = 0`. -/
theorem polar_lebesgueSingularPart_eq_symmTensor_orth {d : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (u : Vec d → Vec d) (Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ))
    (hEu : IsBDGradientOn Ω u Eu)
    (hdiv : ∃ g : Vec d → ℝ, MemLp g 2 (volume.restrict Ω) ∧
      ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
        ∫ x in Ω, ∑ i, u x i * euclideanCoordDeriv i φ x = -∫ x in Ω, g x * φ x) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      ∃ a : Vec d, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧ vecDot a b = 0 ∧
        polar (lebesgueSingularPart Eu) x = fun p => (a p.1 * b p.2 + b p.1 * a p.2) / 2 := by exact AFree.BDOrthProof.result Ω hΩ u Eu hEu hdiv

end AFree
