module

public import AFree.Paper.SimpleAE

/-!
# Proof of [DPR, Remark 1.11]
-/

public section

open MeasureTheory

namespace AFree.SimpleAEProof

open AFree PDE

/-- [DPR, Remark 1.11]: the polar of a locally normal `(d-2)`-current is simple at `τ^s`-a.e. point. -/
theorem result {d : ℕ} (τ : Measure (Vec d))
    (P : Vec d → KVec d (d - 2)) (hT : IsLocNormalCurrent τ P) :
    ∀ᵐ x ∂τ.singularPart volume, IsSimpleKVec (P x) :=
  simpleae hT

end AFree.SimpleAEProof
