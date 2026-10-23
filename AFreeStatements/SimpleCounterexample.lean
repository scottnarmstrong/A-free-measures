module

public import AFree.Defs
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import AFree.Proofs.SimpleCounterexampleProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Remark 1.11], the example in `ℝ⁵`: `T⃗ = (e₁ ∧ e₂ + e₃ ∧ e₄)/√2` and
`‖T‖ = √2 𝓗⁴ ⌞ {x₅ = 0}` define a locally normal `2`-current whose polar is not simple
`‖T‖ˢ`-almost everywhere. Here `μH[4]` is Mathlib's Hausdorff measure for the sup metric of `Vec 5`;
on the hyperplane `{x₅ = 0}` it equals `𝓛⁴`, that is, the Euclidean `𝓗⁴`. -/
theorem not_ae_isSimpleKVec_example :
    ∃ P : Vec 5 → KVec 5 2,
      (∀ x, P x = fun I => if I.1 = {0, 1} ∨ I.1 = {2, 3} then (Real.sqrt 2)⁻¹ else 0) ∧
      IsLocNormalCurrent
        (ENNReal.ofReal (Real.sqrt 2) • (μH[4] : Measure (Vec 5)).restrict {x | x 4 = 0}) P ∧
      ¬ ∀ᵐ x ∂(ENNReal.ofReal (Real.sqrt 2) •
          (μH[4] : Measure (Vec 5)).restrict {x | x 4 = 0}).singularPart volume,
        IsSimpleKVec (P x) := by exact AFree.SimpleCounterexampleProof.result

end AFree
