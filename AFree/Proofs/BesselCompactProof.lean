module

public import AFree.Paper.Bessel

/-!
# Proof of [DPR, Lemma 2.1]

The Bessel potential is a compact operator from `L¹`-bounded functions into `L^p`, by `Bessel.bessel_compact`.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree.BesselCompactProof

/-- [DPR, Lemma 2.1]: the Bessel potential of order `s` is a compact operator from the `L¹` ball to `L^p` for `p` below the critical exponent. -/
theorem result {d : ℕ} {s : ℝ} (hs : 0 < s) {p : ENNReal}
    [Fact (1 ≤ p)] (hp : p < besselExponent d s) :
    ∃ T : L1Ball d →L[ℝ] Lp ℝ p (volume : Measure (Vec d)), IsCompactOperator T ∧
      ∀ u : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → tsupport u ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ f : L1Ball d, ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume] u →
          ((T f : Lp ℝ p (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume]
            fun x => (besselPotential s u x).re :=
  Bessel.bessel_compact hs hp

end AFree.BesselCompactProof
