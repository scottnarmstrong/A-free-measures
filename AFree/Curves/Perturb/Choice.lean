module

public import AFree.Curves.Perturb.Step1
public import AFree.Curves.Perturb.GLem
public import AFree.Curves.Perturb.MollifyDeriv

/-!
# Choice of the parameters in [AM, Proposition 7.4]: `δ`, `A`, `g` and `ρ`
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- For a compact `C(e, α)`-null `K` and `ε > 0` there are
`δ ∈ (0, 1]`, a continuous `g` (the function `perturbG` for `A` the open `δ`-neighbourhood of `K`,
whose smallness hypothesis holds by the uniform smallness lemma) with `0 ≤ g ≤ ε`, the monotonicity and
slope bounds along `e`, the Lipschitz bound along `e^⊥`, and a smooth
`ρ ≥ 0`, `∫ ρ = 1`, with compact support in the Euclidean ball `B(δ/3)`. -/
theorem perturb_choice_of_data {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {K : Set (Vec d)} (hK : IsCompact K) (hnull : IsCNull (cone e α) K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (g ρ : Vec d → ℝ), 0 < δ ∧ δ ≤ 1 ∧ Continuous g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ ε) ∧
      (∀ z, ∀ s : ℝ, 0 ≤ s → g z ≤ g (z + s • e) ∧ g (z + s • e) ≤ g z + s) ∧
      (∀ z, ∀ s : ℝ, 0 ≤ s → (∀ σ ∈ Icc 0 s, z + σ • e ∈ perturbOpenNbhd K δ) →
        g (z + s • e) = g z + s) ∧
      (∀ z v, vecDot v e = 0 → |g (z + v) - g z| ≤ vecEuclideanNorm v / Real.tan α) ∧
      ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ y, 0 ≤ ρ y) ∧ ∫ y, ρ y = 1 ∧
      (∀ y, ρ y ≠ 0 → vecEuclideanNorm y ≤ δ / 3) := by
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := perturb_step1 he hα hα2 hK hnull hε
  have hA : ∀ a b η, IsConeGraphFn e α a b η →
      perturbMeas e (perturbOpenNbhd K δ) a b η ≤ ENNReal.ofReal ε := by
    intro a b η hη
    have hsub : Icc a b ∩ {u | graphCurve e η u ∈ perturbOpenNbhd K δ} ⊆
        Icc a b ∩ {u | graphCurve e η u ∈ perturbClosedNbhd K δ} :=
      fun u ⟨hu, hP⟩ => ⟨hu, perturbOpenNbhd_subset_closed K le_rfl hP⟩
    exact (measure_mono hsub).trans (hδ a b η hη)
  obtain ⟨hb, hm, hc, -, hcont, -⟩ := perturb_g he hα hα2 hε.le hA
  -- the mollifier
  have hd1 : (0 : ℝ) < 3 * ((d : ℝ) + 1) := by positivity
  have hr : 0 < δ / (3 * ((d : ℝ) + 1)) := by positivity
  let b : ContDiffBump (0 : Vec d) :=
    { rIn := δ / (3 * ((d : ℝ) + 1)) / 2
      rOut := δ / (3 * ((d : ℝ) + 1))
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨δ, perturbG e α (perturbOpenNbhd K δ), b.normed volume, hδ0, hδ1, hcont, hb,
    fun z s hs => ⟨(hm z s hs).1, (hm z s hs).2.1⟩, fun z s hs h => (hm z s hs).2.2 h, hc,
    b.contDiff_normed, b.hasCompactSupport_normed, b.nonneg_normed, b.integral_normed, ?_⟩
  intro y hy
  have hy' : y ∈ Metric.ball (0 : Vec d) b.rOut := by
    rw [← b.support_normed_eq (μ := volume)]; exact hy
  rw [mem_ball_zero_iff] at hy'
  have h1 := vecEuclideanNorm_le_sqrt_natCast_mul_norm y
  have h2 : Real.sqrt d ≤ (d : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h3 : Real.sqrt d * ‖y‖ ≤ ((d : ℝ) + 1) * b.rOut :=
    mul_le_mul h2 hy'.le (norm_nonneg _) (by positivity)
  have h4 : ((d : ℝ) + 1) * b.rOut = δ / 3 := by
    show ((d : ℝ) + 1) * (δ / (3 * ((d : ℝ) + 1))) = δ / 3
    field_simp
  linarith

end AFree
