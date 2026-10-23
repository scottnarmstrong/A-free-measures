module

public import AFree.Paper.Currents.System

/-!
# The system holds and lives in `Ω`

The block measures of a family of normal currents and of their boundaries satisfy the system `𝒜𝐓 = σ`
and are concentrated in `Ω`, as needed for [DPR, Theorem 1.10].
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {d r : ℕ}

/-- A test function is measurable and bounded. -/
theorem IsTestFunctionOn.measurable_bound {Ω : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsTestFunctionOn Ω φ) : Measurable φ ∧ ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C := by
  have hc : Continuous φ := hφ.1.continuous
  exact ⟨hc.measurable, hc.bounded_above_of_compact_support hφ.2.1⟩

/-- Derivatives of test functions are test functions. -/
theorem IsTestFunctionOn.coordDeriv {Ω : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsTestFunctionOn Ω φ) (m : Fin d) : IsTestFunctionOn Ω (euclideanCoordDeriv m φ) :=
  ⟨contDiff_euclideanCoordDeriv hφ.1 m, hasCompactSupport_euclideanCoordDeriv hφ.2.1 m,
    (tsupport_euclideanCoordDeriv_subset_tsupport m φ).trans hφ.2.2⟩

/-- The block measures `𝐓`, `σ` of `(Tᵢ)`, `(Sᵢ)` live in `Ω` and satisfy
`A₀ ∫ φ d𝐓 - ∫ φ dσ = Σ_ℓ A_ℓ ∫ ∂_ℓ φ d𝐓` (with `A₀ = 0`) for every test function `φ`. -/
theorem blockMeasure_system_free {Ω : Set (Vec d)} (k : Fin r → ℕ)
    (T : (i : Fin r) → VectorMeasure (Vec d) (KVec d (k i)))
    (S : (i : Fin r) → VectorMeasure (Vec d) (KVec d (k i - 1)))
    (hT : ∀ i, euclideanVariation (T i) Ωᶜ = 0) (hS : ∀ i, IsBoundaryOn Ω (T i) (S i)) :
    euclideanVariation (blockMeasure T) Ωᶜ = 0 ∧ euclideanVariation (blockMeasure S) Ωᶜ = 0 ∧
      ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
        (0 : Matrix (Σ i, KIdx d (k i - 1)) (Σ i, KIdx d (k i)) ℝ) *ᵥ
            (∫ᵛ x, φ x ∂•(blockMeasure T)) - (∫ᵛ x, φ x ∂•(blockMeasure S)) =
          ∑ ℓ, systemCoeff k ℓ *ᵥ (∫ᵛ x, euclideanCoordDeriv ℓ φ x ∂•(blockMeasure T)) := by
  refine ⟨euclideanVariation_blockMeasure_eq_zero T hT,
    euclideanVariation_blockMeasure_eq_zero S fun i => (hS i).1, fun φ hφ => ?_⟩
  obtain ⟨hm, C, hC⟩ := hφ.measurable_bound
  funext ⟨i, J⟩
  rw [zero_mulVec, Pi.sub_apply, Pi.zero_apply, zero_sub,
    integral_blockMeasure_apply S hm hC i J, (hS i).2 φ hφ J, systemCoeff_sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases h : (insert ℓ J.1).card = k i
  · obtain ⟨hm', C', hC'⟩ := (hφ.coordDeriv ℓ).measurable_bound
    simp only [h, ↓reduceDIte]
    rw [integral_blockMeasure_apply T hm' hC' i]
  · simp only [h, ↓reduceDIte]

end AFree
