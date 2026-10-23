module

public import AFree.Paper.Counterexample

/-!
# The counterexample of [DPR, Remark 1.11] in `ℝ⁵`

A locally normal 2-current in `ℝ⁵` whose polar is not a.e. simple.
-/

public section

open MeasureTheory

namespace AFree.SimpleCounterexampleProof

open PDE

/-- [DPR, Remark 1.11]: a locally normal 2-current in `ℝ⁵` with a non-simple polar on a singular set. -/
theorem result :
    ∃ P : Vec 5 → KVec 5 2,
      (∀ x, P x = fun I => if I.1 = {0, 1} ∨ I.1 = {2, 3} then (Real.sqrt 2)⁻¹ else 0) ∧
      IsLocNormalCurrent
        (ENNReal.ofReal (Real.sqrt 2) • (μH[4] : Measure (Vec 5)).restrict {x | x 4 = 0}) P ∧
      ¬ ∀ᵐ x ∂(ENNReal.ofReal (Real.sqrt 2) •
          (μH[4] : Measure (Vec 5)).restrict {x | x 4 = 0}).singularPart volume,
        IsSimpleKVec (P x) :=
  counterex

end AFree.SimpleCounterexampleProof
