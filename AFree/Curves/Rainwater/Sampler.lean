module

public import Mathlib.Probability.Kernel.Representation
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# The sampler lemma

Mathlib's
`MeasureTheory.Measure.exists_measurable_map_eq` is the quantile-function construction.
-/

public section

open MeasureTheory
open scoped unitInterval

namespace AFree

/-- For a Borel probability measure `τ` on a Polish space `Y` there is a Borel map
`ζ : [0,1] → Y` pushing Lebesgue measure on `[0,1]` onto `τ`. -/
theorem exists_measurable_map_unitInterval_eq {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (τ : Measure Y) [IsProbabilityMeasure τ] :
    ∃ ζ : unitInterval → Y, Measurable ζ ∧ Measure.map ζ volume = τ :=
  haveI : Nonempty Y := τ.nonempty_of_neZero
  Measure.exists_measurable_map_eq τ

end AFree
