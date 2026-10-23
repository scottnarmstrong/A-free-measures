module

public import AFree.Defs
public import AFree.Measure.VectorIntegral

/-!
# 𝒜-free pairs

A vector measure `μ` that is first-order 𝒜-free gives the 𝒜-free pair `(|μ|, dμ/d|μ|)`.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `(σ,P)` is `𝒜`-free in `Ω`. -/
def IsFreePair {d : ℕ} (Ω : Set (Vec d)) (A : Fin d → Matrix κ ι ℝ) (A₀ : Matrix κ ι ℝ)
    (σ : Measure (Vec d)) (P : Vec d → ι → ℝ) : Prop :=
  σ Ωᶜ = 0 ∧ ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
    A₀ *ᵥ (∫ x, φ x • P x ∂σ) = ∑ ℓ, A ℓ *ᵥ (∫ x, euclideanCoordDeriv ℓ φ x • P x ∂σ)

theorem IsTestFunctionOn.bounded {d : ℕ} {Ω : Set (Vec d)} {φ : Vec d → ℝ}
    (h : IsTestFunctionOn Ω φ) : Measurable φ ∧ ∃ C, ∀ x, ‖φ x‖ ≤ C := by
  have hc : Continuous φ := h.1.continuous
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support h.2.1
  exact ⟨hc.measurable, C, hC⟩

theorem IsTestFunctionOn.coordDeriv_bounded {d : ℕ} {Ω : Set (Vec d)} {φ : Vec d → ℝ}
    (h : IsTestFunctionOn Ω φ) (ℓ : Fin d) :
    Measurable (euclideanCoordDeriv ℓ φ) ∧ ∃ C, ∀ x, ‖euclideanCoordDeriv ℓ φ x‖ ≤ C := by
  have hc : Continuous (euclideanCoordDeriv ℓ φ) := by
    unfold euclideanCoordDeriv
    exact (h.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (euclideanCoordDeriv ℓ φ) := by
    unfold euclideanCoordDeriv
    exact (h.2.1.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec ℓ)) (by simp)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨hc.measurable, C, hC⟩

omit [Fintype κ] in
/-- A first-order 𝒜-free vector measure gives the 𝒜-free pair
`(|μ|, dμ/d|μ|)`. -/
theorem isFreePair_of_isFirstOrderFree {d : ℕ} {Ω : Set (Vec d)} {A : Fin d → Matrix κ ι ℝ}
    {A₀ : Matrix κ ι ℝ} {μ : VectorMeasure (Vec d) (ι → ℝ)}
    (hμ : euclideanVariation μ Ωᶜ = 0) (h : IsFirstOrderFree Ω A A₀ μ) :
    IsFreePair Ω A A₀ (euclideanVariation μ) (polar μ) := by
  refine ⟨hμ, fun φ hφ => ?_⟩
  have := h φ hφ
  obtain ⟨hm, C, hC⟩ := hφ.bounded
  rw [integral_smul_vectorMeasure_eq μ hm hC] at this
  rw [this]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  obtain ⟨hm', C', hC'⟩ := hφ.coordDeriv_bounded ℓ
  rw [integral_smul_vectorMeasure_eq μ hm' hC']

end AFree
