module

public import AFree.Defs
public import AFree.Paper.OrderK.MainBD

/-!
# Proof of [DPR, Corollary 1.8]

The symmetrized-tensor assembly `polar_lebesgueSingularPart_eq_symmTensor_orth_of_main`, with its
hypothesis on the wave cone supplied by [DPR, Theorem 1.1] of order `2` for the Saint-Venant operator.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree.BDOrthProof

open PDE

/-- [DPR, Corollary 1.8]: for `u ∈ BD` with `div u ∈ L²`, the polar of `E u` is `a ⊙ b` with `a ⊥ b`. -/
theorem result {d : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (u : Vec d → Vec d) (Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ))
    (hEu : IsBDGradientOn Ω u Eu)
    (hdiv : ∃ g : Vec d → ℝ, MemLp g 2 (volume.restrict Ω) ∧
      ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
        ∫ x in Ω, ∑ i, u x i * euclideanCoordDeriv i φ x = -∫ x in Ω, g x * φ x) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      ∃ a : Vec d, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧ vecDot a b = 0 ∧
        polar (lebesgueSingularPart Eu) x = fun p => (a p.1 * b p.2 + b p.1 * a p.2) / 2 :=
  polar_lebesgueSingularPart_eq_symmTensor_orth_of_main hΩ hEu hdiv
    (polar_mem_waveCone_saintVenant hΩ hEu)

end AFree.BDOrthProof
