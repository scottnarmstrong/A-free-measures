module

public import AFree.Curves.Bundle.Exists

/-!
# Existence of the decomposability bundle [AM, Lemma 2.3]
-/

public section

open MeasureTheory

namespace AFree.DecompBundleExistsProof

open AFree PDE

/-- [AM, Lemma 2.3]: the decomposability bundle of a finite measure exists. -/
theorem result {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    ∃ V, IsDecompBundle μ V :=
  Bundle.bundle_exists μ

end AFree.DecompBundleExistsProof
