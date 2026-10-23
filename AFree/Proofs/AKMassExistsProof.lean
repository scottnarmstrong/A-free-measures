module

public import AFree.MetricCurrents.AKMass

/-!
# Existence of the mass of a metric functional [AK, Definition 2.6]

A metric functional that admits a finite mass measure has a mass `‖T‖`, the minimal such measure.
The proof is `AFree.akmass`.
-/

public section

open MeasureTheory

namespace AFree.AKMassExistsProof

open PDE

/-- The mass `‖T‖` of a metric functional with finite admissible measure exists. -/
theorem result {d k : ℕ} (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ)
    (hT : IsMetricFunctional k T) (hfin : ∃ μ, IsAKMassAdmissible T μ) :
    ∃ μ, IsAKMass T μ :=
  (akmass hT hfin).1

end AFree.AKMassExistsProof
