module

public import AFree.Defs
public import AFree.Proofs.SimpleAEProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Remark 1.11]: for a locally normal `(d-2)`-current `T = T⃗ ‖T‖` on `ℝ^d`, the polar
`T⃗(x)` is simple for `‖T‖ˢ`-almost every `x`. -/
theorem ae_isSimpleKVec_of_isLocNormalCurrent {d : ℕ} (τ : Measure (Vec d))
    (P : Vec d → KVec d (d - 2)) (hT : IsLocNormalCurrent τ P) :
    ∀ᵐ x ∂τ.singularPart volume, IsSimpleKVec (P x) := by exact AFree.SimpleAEProof.result τ P hT

end AFree
