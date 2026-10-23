module

public import AFree.Paper.Currents.Covector
public import AFree.Algebra.KVec.Equiv
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Corollary 1.9: boundaryless `(d-1)`-currents

[DPR, Corollary 1.9] is [DPR, Theorem 1.10] with `Ω = ℝᵈ`, `kᵢ = d - 1`, `∂Tᵢ = 0`, together with the
fact that `v ⌟ ω = 0` for `ω ≠ 0` iff the `(d-1)`-vector `v` lies in `Λ_{d-1}(ker ω)`.
-/

public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {d r : ℕ}

/-- Boundaryless `(d-1)`-currents on `ℝᵈ` are normal currents on `ℝᵈ` with `kᵢ = d - 1`
and `Sᵢ = 0`, so [DPR, Theorem 1.10] applies (for `d ≥ 2`). -/
theorem ae_exists_covector_of_boundaryless (hd : 2 ≤ d)
    (T : Fin r → VectorMeasure (Vec d) (KVec d (d - 1)))
    (hT : ∀ i, IsBoundaryOn Set.univ (T i) 0)
    (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ i, μ ≪ euclideanVariation (T i)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ ω : Vec d, ω ≠ 0 ∧
      ∀ i, interiorProduct (polar (T i) x) ω = 0 :=
  ae_exists_covector_interiorProduct_eq_zero Set.univ isOpen_univ (fun _ => d - 1)
    (fun _ => ⟨by omega, by omega⟩) T
    (fun i => ⟨by simp, 0, hT i⟩) μ (by simp)
    (fun K hK _ => hK.measure_lt_top) hμ

/-- [DPR, Corollary 1.9]: for `μˢ`-a.e. `x` there is a hyperplane `V` with
`polar(Tᵢ)(x) ∈ Λ_{d-1}(V)` for all `i`. -/
theorem ae_exists_hyperplane_of_boundaryless
    (T : Fin r → VectorMeasure (Vec d) (KVec d (d - 1)))
    (hT : ∀ i, IsBoundaryOn Set.univ (T i) 0)
    (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ i, μ ≪ euclideanVariation (T i)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ V : Submodule ℝ (Vec d), Module.finrank ℝ V = d - 1 ∧
      ∀ i, polar (T i) x ∈ kvecSpan V (d - 1) := by
  rcases lt_or_ge d 2 with hd | hd
  · refine Filter.Eventually.of_forall fun x => ⟨⊥, ?_, fun i => ?_⟩
    · rw [finrank_bot]; omega
    · have key : ∀ m, m = 0 → ∀ v : KVec d m, v ∈ kvecSpan (⊥ : Submodule ℝ (Vec d)) m := by
        rintro m rfl v
        rw [(kzero (d := d)).2.2]
        trivial
      exact key _ (by omega) _
  · filter_upwards [ae_exists_covector_of_boundaryless hd T hT μ hμ] with x ⟨ω, hω, h⟩
    refine ⟨covectorKernel ω, finrank_covectorKernel ω hω, fun i => ?_⟩
    exact (equiv_interiorProduct_kvecSpan (by omega) ω hω _).1 (h i)

end AFree
