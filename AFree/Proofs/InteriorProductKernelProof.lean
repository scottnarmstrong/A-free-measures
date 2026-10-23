module

public import AFree.Algebra.KVec

@[expose] public section

namespace AFree.InteriorProductKernelProof

open PDE AFree

/-- [DPR, Theorem 1.10], "Equivalently": `v ⌟ ω = 0 ↔ v ∈ Λ_k(ker ω)`. -/
theorem result {d k : ℕ} (hk : 1 ≤ k) (ω : Vec d) (hω : ω ≠ 0)
    (v : KVec d k) :
    interiorProduct v ω = 0 ↔ v ∈ kvecSpan (covectorKernel ω) k :=
  equiv_interiorProduct_kvecSpan hk ω hω v

end AFree.InteriorProductKernelProof
