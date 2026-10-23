module

public import AFree.Defs
public import AFree.Proofs.FlatChainProof

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval

namespace AFree

open PDE

/-- [DPR, Theorem 1.15], identification of metric `d`-currents with flat `d`-chains, for compactly
supported currents as in [AK, Theorem 11.1]. A compactly supported metric current `T` and a flat chain
`S` correspond when `∫ f dS = T(f, x₁, …, x_d)` for smooth compactly supported `f`. Every such `T`
has a corresponding flat chain, every flat chain corresponds to such a `T`, and `T` is determined by
these values. -/
theorem isTopFlatChain_iff_isMetricCurrent {d : ℕ} :
    (∀ T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ, IsMetricCurrent d T → HasCompactAKSupport T →
      ∃ S, IsTopFlatChain S ∧ ∀ f, IsTestFunctionOn Set.univ f →
        (∫ᵛ x, f x ∂•S) (topKIdx d) = T f (fun i x => x i)) ∧
    (∀ S, IsTopFlatChain S → ∃ T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ,
      IsMetricCurrent d T ∧ HasCompactAKSupport T ∧ ∀ f, IsTestFunctionOn Set.univ f →
        (∫ᵛ x, f x ∂•S) (topKIdx d) = T f (fun i x => x i)) ∧
    (∀ T₁ T₂ : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ, IsMetricCurrent d T₁ →
      HasCompactAKSupport T₁ → IsMetricCurrent d T₂ → HasCompactAKSupport T₂ →
      (∀ f, IsTestFunctionOn Set.univ f → T₁ f (fun i x => x i) = T₂ f (fun i x => x i)) →
      ∀ f, IsBddLipFun f → ∀ π : Fin d → Vec d → ℝ, (∀ i, IsLipFun (π i)) → T₁ f π = T₂ f π) := by exact AFree.FlatChainProof.result

end AFree
