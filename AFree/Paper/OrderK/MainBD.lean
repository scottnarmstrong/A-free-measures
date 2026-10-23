module

public import AFree.Paper.OrderK.Main
public import AFree.Paper.BD.Assembly

/-!
# The hypothesis `hmain` of the BD assemblies

Theorem 1.1 for `k = 2` and the Saint-Venant operator, applied to `Eu` (the freeness of `Eu` is
proved separately), discharges the hypothesis of the conditional assemblies of `AFree.Paper.BD`.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

variable {d : ℕ}

/-- The instance of Theorem 1.1 with `k = 2` and the
Saint-Venant operator: `polar Eu ∈ Λ_{saintVenant}` at `|Eu|ˢ`-a.e. point. -/
theorem polar_mem_waveCone_saintVenant {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {u : Vec d → Vec d}
    {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)} (hEu : IsBDGradientOn Ω u Eu) :
    ∀ᵐ x ∂(euclideanVariation Eu).singularPart volume, polar Eu x ∈ waveCone 2 saintVenant :=
  thm_general Ω hΩ saintVenant Eu hEu.2.1 (isFree_saintVenant_of_isBDGradientOn hEu)

end AFree
