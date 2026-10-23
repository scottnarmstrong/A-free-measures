module

public import AFree.Defs
public import AFree.Paper.OrderK.MainBD

/-!
# Proof of [DPR, Theorem 1.7]

The symmetrized-tensor assembly `polar_lebesgueSingularPart_eq_symmTensor_of_main`, with its
hypothesis on the wave cone supplied by [DPR, Theorem 1.1] of order `2` for the Saint-Venant operator.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree.BDProof

open PDE

/-- [DPR, Theorem 1.7]: for `u ∈ BD`, the polar of the singular part of `E u` is a symmetric tensor `a ⊙ b`. -/
theorem result {d : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (u : Vec d → Vec d) (Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ))
    (hEu : IsBDGradientOn Ω u Eu) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      ∃ a : Vec d, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Eu) x = fun p => (a p.1 * b p.2 + b p.1 * a p.2) / 2 :=
  polar_lebesgueSingularPart_eq_symmTensor_of_main hΩ hEu (polar_mem_waveCone_saintVenant hΩ hEu)

end AFree.BDProof
