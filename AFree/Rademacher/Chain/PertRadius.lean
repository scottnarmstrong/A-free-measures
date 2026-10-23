module

public import AFree.Rademacher.Chain.PertSetup
public import AFree.Rademacher.Chain.PertClaimB

/-!
# The radius `r_*(x̄)` of the single-stage perturbation

Choice of the local radius in the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE Filter Topology Set

namespace AFree.Rademacher

variable {d : ℕ}

/-- Step 3: for every base point `p` there is `R > 0` (below `σ/4` and `c`) such that for all
`r < R` the local data hold with `ω = θ = c/4` and `ρ = c/2`. -/
theorem pert_radius {e : Vec d → Fin d → Vec d} (he : IsFrame e) {f : Vec d → ℝ}
    (hf : f ∈ X0 e) {s c σ : ℝ} (hs0 : 0 < s) (hs2 : s ≤ 1 / 2) (hc : 0 < c) (hc8 : c ≤ 1 / 8)
    (hc1 : (2 + Real.sqrt d) * c ≤ s / 2) (hc2 : 3 * c ≤ s) (hσ : 0 < σ)
    (hfb : ∀ x j, |fderiv ℝ f x (e x j)| ≤ 1 - s) (p : Vec d) :
    ∃ R : ℝ, 0 < R ∧ R ≤ σ / 4 ∧ R ≤ c ∧ ∀ r, 0 < r → r < R →
      LocalData e f p r s (c / 4) (c / 4) (c / 2) := by
  obtain ⟨η, hη, hηP⟩ := exists_local_radius he hf.1 p (ω := c / 4) (θ := c / 4) (by positivity)
    (by positivity)
  refine ⟨min (σ / 4) (min c (η / 5)), lt_min (by positivity) (lt_min hc (by positivity)),
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), fun r hr hrR => ?_⟩
  have hrη : r < η / 5 := hrR.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsq := Real.sqrt_nonneg (d : ℝ)
  refine ⟨he, hr, hs0, hs2, hf.1.differentiable (by simp), hfb,
    (X0_lipschitz he).1 f hf p, fun y hy => (hηP y (by linarith)).1,
    fun y hy => (hηP y (by linarith)).2, by positivity, by positivity, by positivity,
    by linarith, ?_, by linarith⟩
  nlinarith

end AFree.Rademacher
