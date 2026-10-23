module

public import AFree.Defs
public import AFree.Proofs.InteriorProductKernelProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Theorem 1.10], the equivalent form of the conclusion: for `k ≥ 1` and `ω ≠ 0`,
`v ⌟ ω = 0` if and only if `v ∈ Λ_k(ker ω)`. -/
theorem interiorProduct_eq_zero_iff_mem_kvecSpan {d k : ℕ} (hk : 1 ≤ k) (ω : Vec d) (hω : ω ≠ 0)
    (v : KVec d k) :
    interiorProduct v ω = 0 ↔ v ∈ kvecSpan (covectorKernel ω) k := by exact AFree.InteriorProductKernelProof.result hk ω hω v

end AFree
