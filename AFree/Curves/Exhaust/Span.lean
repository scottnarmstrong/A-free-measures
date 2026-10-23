module

public import AFree.Curves.Exhaust.Polar
public import AFree.Curves.Exhaust.CurveNormal
public import AFree.Curves.Exhaust.Indep
public import AFree.Proofs.SpanAbsContProof

/-!
# Curve currents give absolute continuity

If finitely many curve mixtures along independent cones dominate `μ⌞P`, then `μ⌞P ≪ vol^d`.
-/

@[expose] public section

open MeasureTheory Set

namespace AFree

open PDE

variable {d : ℕ}

/-- Let `μ` be finite, `P` Borel, `C_j = C(w_j, β_j)` cones with nearly independent axes
and `ρ_j` finite measures on `𝒢(C_j)` with `μ⌞P ≪ [ρ_j]`. Then `μ⌞P ≪ vol^d`. -/
theorem spanac_prop {μ : Measure (Vec d)} [IsFiniteMeasure μ] {P : Set (Vec d)}
    {w : Fin d → Vec d} (hw : ∀ j, vecEuclideanNorm (w j) = 1) {η : ℝ}
    (hlow : ∀ a : Vec d, η * vecEuclideanNorm a ≤ vecEuclideanNorm (∑ j, a j • w j))
    {β : Fin d → ℝ} (hβ : ∀ j, 0 < β j ∧ β j < Real.pi / 2)
    (hβη : ∀ j, Real.sqrt d * β j < η)
    (ρ : ∀ j, Measure (ccurveSpace (w j) (β j))) [∀ j, IsFiniteMeasure (ρ j)]
    (hμ : ∀ j, μ.restrict P ≪ curveMix (ccurveSpace (w j) (β j)) (ρ j)) :
    μ.restrict P ≪ volume := by
  refine SpanAbsContProof.result (fun j => curveCurrent (w j) (β j) (ρ j))
    (fun j => (isNormalCurrentOn_curveCurrent (hβ j).1 (hβ j).2 (ρ j)).1) (μ.restrict P)
    (fun j => (hμ j).trans (curveCurrent_mass_lower (hw j) (hβ j).1 (hβ j).2 (ρ j)).2) ?_
  have hpol : ∀ j, ∀ᵐ x ∂(μ.restrict P),
      kvecOneToVec (polar (curveCurrent (w j) (β j) (ρ j)) x) ∈ cone (w j) (β j) ∧
        kvecOneToVec (polar (curveCurrent (w j) (β j) (ρ j)) x) ≠ 0 := fun j =>
    (curveCurrent_polar (hw j) (hβ j).1 (hβ j).2 (ρ j)).2.2 _ (hμ j)
  filter_upwards [ae_all_iff.2 hpol] with x hx
  exact (indep_cones hw hlow hβ hβη (fun j => (hx j).1) (fun j => (hx j).2)).2

end AFree
