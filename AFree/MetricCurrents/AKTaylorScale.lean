module

public import AFree.MetricCurrents.AKTaylorBasic
public import AFree.MetricCurrents.Grid

/-!
# Taylor lemma, Step 1: the scale and the grid
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKTaylor

open PDE AFree

variable {k : ℕ}

/-- Step 1. For `δ > 0` and `R` there is a scale `r ∈ (0, 1]` such that
`Dψ` oscillates by at most `δ` at distance `≤ 2r` inside the ball `‖y‖ ≤ R + 4` (uniform continuity on
a compact set), and the finite set `F` of grid indices `J` whose `χ_J` does not vanish identically on
`{‖y‖ ≤ R + 1}`. -/
theorem scale_and_grid {ψ : Fin k → Vec k → ℝ} (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (R : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      (∀ y y' : Vec k, ‖y‖ ≤ R + 4 → ‖y'‖ ≤ R + 4 → ‖y - y'‖ ≤ 2 * r → ∀ i,
        ‖fderiv ℝ (ψ i) y - fderiv ℝ (ψ i) y'‖ ≤ δ) ∧
      ∃ F : Finset (Fin k → ℤ), ∀ J, J ∈ F ↔ ∃ y : Vec k, ‖y‖ ≤ R + 1 ∧ gridChi r J y ≠ 0 := by
  have hcont : Continuous fun (y : Vec k) (i : Fin k) => fderiv ℝ (ψ i) y :=
    continuous_pi fun i => (hψ i).continuous_fderiv one_ne_zero
  have huc := (isCompact_closedBall (0 : Vec k) (R + 4)).uniformContinuousOn_of_continuous
    hcont.continuousOn
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.uniformContinuousOn_iff.1 huc δ hδ
  have hr : 0 < min 1 (ρ / 4) := lt_min one_pos (by positivity)
  refine ⟨min 1 (ρ / 4), hr, min_le_left _ _, ?_, ?_⟩
  · intro y y' hy hy' hyy i
    have h1 : dist y y' < ρ := by
      rw [dist_eq_norm]
      have := min_le_right 1 (ρ / 4)
      linarith
    have h2 := hρ' y (by simpa using hy) y' (by simpa using hy') h1
    have h3 := (dist_le_pi_dist (fun i => fderiv ℝ (ψ i) y) (fun i => fderiv ℝ (ψ i) y') i)
    rw [dist_eq_norm] at h3
    exact (h3.trans h2.le)
  · have hfin := (grid_partition_of_unity (m := k) hr).2.2.2.2.2 (R + 1)
    exact ⟨hfin.toFinset, fun J => by simp⟩

end AFree.MetricCurrents.AKTaylor
