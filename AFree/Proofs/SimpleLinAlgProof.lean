module

public import AFree.Algebra.KVec

@[expose] public section

namespace AFree.SimpleLinAlgProof

open PDE AFree

/-- [DPR, Remark 1.11] (linear algebra): `Λ_{d-2}(V)` consists of simple vectors
when `dim V = d - 1`. -/
theorem result {d : ℕ} (V : Submodule ℝ (Vec d))
    (hV : Module.finrank ℝ V = d - 1) (w : KVec d (d - 2)) (hw : w ∈ kvecSpan V (d - 2)) :
    IsSimpleKVec w :=
  simplelin V hV w hw

end AFree.SimpleLinAlgProof
