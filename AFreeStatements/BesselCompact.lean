module

public import AFree.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import AFree.Proofs.BesselCompactProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Lemma 2.1]: for `s > 0` and `1 ≤ p < p(d, s)`, the Bessel potential `(Id - Δ)^{-s/2}`,
applied to smooth functions supported in the unit ball, extends to a compact operator `L¹_c(B₁) → L^p`. -/
theorem exists_compact_besselPotential {d : ℕ} {s : ℝ} (hs : 0 < s) {p : ENNReal}
    [Fact (1 ≤ p)] (hp : p < besselExponent d s) :
    ∃ T : L1Ball d →L[ℝ] Lp ℝ p (volume : Measure (Vec d)), IsCompactOperator T ∧
      ∀ u : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → tsupport u ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ f : L1Ball d, ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume] u →
          ((T f : Lp ℝ p (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume]
            fun x => (besselPotential s u x).re := by exact AFree.BesselCompactProof.result hs hp

end AFree
