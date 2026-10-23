module

public import AFree.TopCurrents.Assembly.Flat

/-!
# Proof of [DPR, Theorem 1.15], flat-chain statement

Top-dimensional flat chains with compact support correspond to metric currents with compact support.
The proof is `AFree.flat_main`.
-/

public section

open MeasureTheory

namespace AFree.FlatChainProof

open PDE

/-- [DPR, Theorem 1.15]: compactly supported metric currents and top-dimensional flat chains correspond. -/
theorem result {d : ℕ} :
    (∀ T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ, IsMetricCurrent d T → HasCompactAKSupport T →
      ∃ S, IsTopFlatChain S ∧ ∀ f, IsTestFunctionOn Set.univ f →
        (∫ᵛ x, f x ∂•S) (topKIdx d) = T f (fun i x => x i)) ∧
    (∀ S, IsTopFlatChain S → ∃ T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ,
      IsMetricCurrent d T ∧ HasCompactAKSupport T ∧ ∀ f, IsTestFunctionOn Set.univ f →
        (∫ᵛ x, f x ∂•S) (topKIdx d) = T f (fun i x => x i)) ∧
    (∀ T₁ T₂ : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ, IsMetricCurrent d T₁ →
      HasCompactAKSupport T₁ → IsMetricCurrent d T₂ → HasCompactAKSupport T₂ →
      (∀ f, IsTestFunctionOn Set.univ f → T₁ f (fun i x => x i) = T₂ f (fun i x => x i)) →
      ∀ f, IsBddLipFun f → ∀ π : Fin d → Vec d → ℝ, (∀ i, IsLipFun (π i)) → T₁ f π = T₂ f π) :=
  flat_main

end AFree.FlatChainProof
