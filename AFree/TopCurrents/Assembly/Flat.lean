module

public import AFree.TopCurrents.Assembly.FlatBack

/-!
# [DPR, Theorem 1.15]: top-dimensional flat chains and metric currents
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

/-- The three statements of the flat-chain identification of [DPR, Theorem 1.15], for every `d`. -/
theorem flat_main {d : ℕ} :
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
  ⟨fun _ hT hK => flat_current_to_chain hT hK, fun _ hS => flat_chain_to_current hS,
    fun _ _ h₁ _ h₂ _ h => flat_uniqueness h₁ h₂ h⟩

end AFree
