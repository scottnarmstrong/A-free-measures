module

public import AFree.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import AFree.Proofs.SimpleLinAlgProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Remark 1.11], linear algebra: if `dim V = d - 1`, every `w ∈ Λ_{d-2}(V)` is simple. -/
theorem isSimpleKVec_of_mem_kvecSpan {d : ℕ} (V : Submodule ℝ (Vec d))
    (hV : Module.finrank ℝ V = d - 1) (w : KVec d (d - 2)) (hw : w ∈ kvecSpan V (d - 2)) :
    IsSimpleKVec w := by exact AFree.SimpleLinAlgProof.result V hV w hw

end AFree
