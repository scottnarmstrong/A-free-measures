module

public import AFree.Defs
public import AFree.Proofs.CovectorKernelProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Theorem 1.10]: for normal currents `T₁, …, T_r` on `Ω` of dimensions `1 ≤ kᵢ ≤ d` and a
measure `μ` on `Ω`, finite on compact subsets, with `μ ≪ ‖Tᵢ‖`, at `μˢ`-almost every point there is a
covector `ω ≠ 0` with `T⃗ᵢ(x) ⌟ ω = 0` for all `i`. -/
theorem exists_covector_interiorProduct_eq_zero {d r : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω) (k : Fin r → ℕ) (hk : ∀ i, 1 ≤ k i ∧ k i ≤ d)
    (T : (i : Fin r) → VectorMeasure (Vec d) (KVec d (k i))) (hT : ∀ i, IsNormalCurrentOn Ω (T i))
    (μ : Measure (Vec d)) (hμΩ : μ Ωᶜ = 0) (hμloc : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤)
    (hμ : ∀ i, μ ≪ euclideanVariation (T i)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ ω : Vec d, ω ≠ 0 ∧
      ∀ i, interiorProduct (polar (T i) x) ω = 0 := by exact AFree.CovectorKernelProof.result Ω hΩ k hk T hT μ hμΩ hμloc hμ

end AFree
