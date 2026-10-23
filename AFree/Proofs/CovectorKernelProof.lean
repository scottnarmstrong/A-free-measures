module

public import AFree.Paper.Currents

/-!
# Proof of [DPR, Theorem 1.10]

The covector `ω` with `polar(T i) ⌟ ω = 0` exists almost everywhere, by `ae_exists_covector_interiorProduct_eq_zero`.
-/

public section

open MeasureTheory

namespace AFree.CovectorKernelProof

open AFree PDE

/-- [DPR, Theorem 1.10]: for normal currents `Tᵢ` and `μ ≪ |Tᵢ|`, at `μ^s`-a.e. `x` some `ω ≠ 0` satisfies `polar(Tᵢ)(x) ⌟ ω = 0` for all `i`. -/
theorem result {d r : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω) (k : Fin r → ℕ) (hk : ∀ i, 1 ≤ k i ∧ k i ≤ d)
    (T : (i : Fin r) → VectorMeasure (Vec d) (KVec d (k i))) (hT : ∀ i, IsNormalCurrentOn Ω (T i))
    (μ : Measure (Vec d)) (hμΩ : μ Ωᶜ = 0) (hμloc : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤)
    (hμ : ∀ i, μ ≪ euclideanVariation (T i)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ ω : Vec d, ω ≠ 0 ∧
      ∀ i, interiorProduct (polar (T i) x) ω = 0 :=
  ae_exists_covector_interiorProduct_eq_zero Ω hΩ k hk T hT μ hμΩ hμloc hμ

end AFree.CovectorKernelProof
