module

public import AFree.Defs
public import AFree.Proofs.DecompBundleIffProof

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval

namespace AFree

open PDE

/-- [DPR, Lemma 3.1]: `V(μ, x) = ℝ^d` for `μ`-almost every `x` if and only if there are normal
`1`-currents `T₁, …, T_d` with `μ ≪ ‖Tᵢ‖` whose polars span `ℝ^d` at `μ`-almost every point. -/
theorem decompBundle_eq_top_iff {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    (∃ V, IsDecompBundle μ V ∧ ∀ᵐ x ∂μ, V x = ⊤) ↔
      ∃ T : Fin d → VectorMeasure (Vec d) (KVec d 1), (∀ i, IsNormalCurrentOn Set.univ (T i)) ∧
        (∀ i, μ ≪ euclideanVariation (T i)) ∧
        ∀ᵐ x ∂μ, Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)) = ⊤ := by exact AFree.DecompBundleIffProof.result μ

end AFree
