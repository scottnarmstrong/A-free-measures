module

public import AFree.Paper.OrderK.Main
public import AFree.Paper.AugmentedMeasure
public import AFree.Paper.OrderK.HarmonicMultideriv

/-!
# A measure on the right-hand side (Remark 1.3)

Reduction to Theorem 1.1 by augmenting the operator with the right-hand side measure.
-/

@[expose] public section

open MeasureTheory Matrix PDE
open scoped Classical

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The augmented coefficients `Ã_α = (A_α | -δ_{α,0} I_κ)` on `ℝ^{ι ⊕ κ}`. -/
def augCoeffK (A : (Fin d → ℕ) → Matrix κ ι ℝ) : (Fin d → ℕ) → Matrix κ (ι ⊕ κ) ℝ :=
  fun α c => Sum.elim (A α c) (fun c' => if α = 0 ∧ c' = c then -1 else 0)

theorem augCoeffK_mulVec (A : (Fin d → ℕ) → Matrix κ ι ℝ) (α : Fin d → ℕ) (R : ι ⊕ κ → ℝ) :
    augCoeffK A α *ᵥ R = A α *ᵥ (fun i => R (Sum.inl i)) -
      (if α = 0 then fun c => R (Sum.inr c) else 0) := by
  funext c
  by_cases hα : α = 0
  · simp [augCoeffK, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hα, sub_eq_add_neg]
  · simp [augCoeffK, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hα]

/-- Let `k ≥ 1`. (a) `Λ^{(k)}_{Ã} = {(v, w) : v ∈ Λ^{(k)}_A}`; (b) `Λ^{(k)}_A` is a
cone; (c) `|μ̃|(Ωᶜ) = 0` and `μ̃ = (μ, σ)` is `Ã`-free in `Ω` as soon as `𝒜μ = σ` in `𝒟'(Ω)`. -/
theorem lem_augop {k : ℕ} (hk : 1 ≤ k) (Ω : Set (Vec d)) (A : (Fin d → ℕ) → Matrix κ ι ℝ) :
    (∀ R : ι ⊕ κ → ℝ, R ∈ waveCone k (augCoeffK A) ↔ (fun i => R (Sum.inl i)) ∈ waveCone k A) ∧
    (∀ v ∈ waveCone k A, ∀ t : ℝ, t • v ∈ waveCone k A) ∧
    ∀ (μ : VectorMeasure (Vec d) (ι → ℝ)) (σ : VectorMeasure (Vec d) (κ → ℝ)),
      euclideanVariation μ Ωᶜ = 0 → euclideanVariation σ Ωᶜ = 0 →
      (∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
        ∑ h ∈ Finset.range (k + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
          (-1 : ℝ) ^ h • (A α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•μ) = ∫ᵛ x, φ x ∂•σ) →
      euclideanVariation (augmentedMeasure μ σ) Ωᶜ = 0 ∧
        IsFree Ω k (augCoeffK A) (augmentedMeasure μ σ) := by
  refine ⟨fun R => ?_, ?_, fun μ σ hμ hσ hrhs => ⟨?_, ?_⟩⟩
  · have h : ∀ ξ : Vec d, (∑ α ∈ Finset.Nat.antidiagonalTuple d k,
        (∏ i, ξ i ^ α i) • augCoeffK A α) *ᵥ R =
        (∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • A α) *ᵥ
          (fun i => R (Sum.inl i)) := by
      intro ξ
      simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, augCoeffK_mulVec]
      refine Finset.sum_congr rfl fun α hα => ?_
      have hα0 : α ≠ 0 := by
        rintro rfl
        have := Finset.Nat.mem_antidiagonalTuple.1 hα
        simp at this
        omega
      simp [hα0]
    constructor
    · rintro ⟨ξ, h1, h2⟩
      exact ⟨ξ, h1, by rw [← h]; exact h2⟩
    · rintro ⟨ξ, h1, h2⟩
      exact ⟨ξ, h1, by rw [h]; exact h2⟩
  · rintro v ⟨ξ, h1, h2⟩ t
    refine ⟨ξ, h1, ?_⟩
    rw [Matrix.mulVec_smul, h2, smul_zero]
  · exact euclideanVariation_augmentedMeasure_compl_eq_zero μ σ hμ hσ
  · intro φ hφ
    have hψ : ∀ α, IsTestFunctionOn Ω (multiCoordDeriv α φ) := fun α =>
      ⟨(isCc_multiCoordDeriv (⟨hφ.1, hφ.2.1⟩ : IsCc φ) α).1,
        (isCc_multiCoordDeriv (⟨hφ.1, hφ.2.1⟩ : IsCc φ) α).2,
        (tsupport_multiCoordDeriv_subset φ α).trans hφ.2.2⟩
    have e1 : ∀ α, ∫ᵛ x, multiCoordDeriv α φ x ∂•(augmentedMeasure μ σ) =
        Sum.elim (∫ᵛ x, multiCoordDeriv α φ x ∂•μ) (∫ᵛ x, multiCoordDeriv α φ x ∂•σ) :=
      fun α => integral_augmentedMeasure_of_isTestFunctionOn μ σ (hψ α)
    simp only [e1, augCoeffK_mulVec, Sum.elim_inl, Sum.elim_inr]
    have h0 : ∀ h ∈ Finset.range (k + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        (-1 : ℝ) ^ h • (A α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•μ -
          (if α = 0 then ∫ᵛ x, multiCoordDeriv α φ x ∂•σ else 0)) =
        ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
          (-1 : ℝ) ^ h • (A α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•μ) -
        (if h = 0 then ∫ᵛ x, φ x ∂•σ else 0) := by
      intro h _
      simp only [smul_sub, Finset.sum_sub_distrib]
      congr 1
      by_cases hh : h = 0
      · subst hh
        simp [Finset.Nat.antidiagonalTuple_zero_right, multiCoordDeriv_zero]
      · simp only [hh, ↓reduceIte]
        refine Finset.sum_eq_zero fun α hα => ?_
        have : α ≠ 0 := by
          rintro rfl
          have := Finset.Nat.mem_antidiagonalTuple.1 hα
          simp at this
          exact hh this.symm
        simp [this]
    refine Eq.trans (Finset.sum_congr rfl h0) ?_
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.range (k + 1)) 0]
    simp only [Finset.mem_range, Nat.succ_pos, ↓reduceIte]
    rw [sub_eq_zero]
    exact hrhs φ hφ

/-- `|μ| ≤ |μ̃|`; a property holding `|μ̃|ˢ`-a.e. holds `|μ|ˢ`-a.e.; and `polar μ̃`
restricted to the first block is a positive multiple of `polar μ`, `|μ|`-a.e. -/
theorem lem_augpolar (μ : VectorMeasure (Vec d) (ι → ℝ)) (σ : VectorMeasure (Vec d) (κ → ℝ)) :
    euclideanVariation μ ≤ euclideanVariation (augmentedMeasure μ σ) ∧
    (∀ p : Vec d → Prop,
      (∀ᵐ x ∂(euclideanVariation (augmentedMeasure μ σ)).singularPart volume, p x) →
        ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, p x) ∧
    ∀ᵐ x ∂euclideanVariation μ, ∃ c : ℝ, 0 < c ∧
      (fun i => polar (augmentedMeasure μ σ) x (Sum.inl i)) = c • polar μ x :=
  ⟨euclideanVariation_le_augmentedMeasure_left μ σ,
    fun _ h => ae_singularPart_of_le (euclideanVariation_le_augmentedMeasure_left μ σ) h,
    polar_augmentedMeasure_inl_proportional μ σ⟩

/-- [DPR, Remark 1.3]: `𝒜μ = σ` with `σ` a measure, order `k ≥ 1`. -/
theorem thm_rhs {k : ℕ} (hk : 1 ≤ k) (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (σ : VectorMeasure (Vec d) (κ → ℝ)) (hσ : euclideanVariation σ Ωᶜ = 0)
    (hrhs : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
      ∑ h ∈ Finset.range (k + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        (-1 : ℝ) ^ h • (A α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•μ) = ∫ᵛ x, φ x ∂•σ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveCone k A := by
  obtain ⟨ha, hb, hc⟩ := lem_augop hk Ω A
  obtain ⟨hμt, hfree⟩ := hc μ σ hμ hσ hrhs
  have hmain := thm_general Ω hΩ (augCoeffK A) (augmentedMeasure μ σ) hμt hfree
  obtain ⟨-, h1, h2⟩ := lem_augpolar μ σ
  have h3 : ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, ∃ c : ℝ, 0 < c ∧
      (fun i => polar (augmentedMeasure μ σ) x (Sum.inl i)) = c • polar μ x :=
    Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ _) h2
  filter_upwards [h1 _ hmain, h3] with x hx ⟨c, hc0, hxc⟩
  rw [ha, hxc] at hx
  have := hb _ hx c⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul] at this

end

end AFree
