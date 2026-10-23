module

public import AFree.Curves.Lemma31

/-!
# Proof of [DPR, Lemma 3.1]
-/

public section

open MeasureTheory Filter Topology

namespace AFree.DecompBundleIffProof

open PDE

/-- [DPR, Lemma 3.1]: the decomposability bundle is a.e. full iff `μ ≪ |Tᵢ|` for normal 1-currents `Tᵢ` whose polars span. -/
theorem result {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    (∃ V, IsDecompBundle μ V ∧ ∀ᵐ x ∂μ, V x = ⊤) ↔
      ∃ T : Fin d → VectorMeasure (Vec d) (KVec d 1), (∀ i, IsNormalCurrentOn Set.univ (T i)) ∧
        (∀ i, μ ≪ euclideanVariation (T i)) ∧
        ∀ᵐ x ∂μ, Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)) = ⊤ :=
  lemma31 μ

end AFree.DecompBundleIffProof
