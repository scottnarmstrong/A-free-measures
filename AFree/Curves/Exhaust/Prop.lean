module

public import AFree.Curves.Exhaust.Remainder

/-!
# Exhaustion by curve mixtures
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- Exhaustion: for a finite Borel measure `μ` on `ℝ^d` and `C = C(e, α)` there
are a finite Borel measure `ρ` on `𝒢(C)` and a Borel `C`-null set `N` with
`μ⌞(ℝ^d ∖ N) ≪ [ρ]` (`curveMix`). -/
theorem exhaust_prop {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    ∃ (ρ : Measure (ccurveSpace e α)) (N : Set (Vec d)), IsFiniteMeasure ρ ∧ MeasurableSet N ∧
      IsCNull (cone e α) N ∧ μ.restrict Nᶜ ≪ curveMix (ccurveSpace e α) ρ := by
  obtain ⟨A₀, hA₀, hmax⟩ := exhaust_maximal e α μ
  obtain ⟨ρ, hρ, hac⟩ := hA₀.2
  obtain ⟨N, hN, hnull, hNac⟩ := exhaust_remainder he hα hα2 hA₀ hmax hac
  exact ⟨ρ, N, hρ, hN, hnull, hNac⟩

end AFree
