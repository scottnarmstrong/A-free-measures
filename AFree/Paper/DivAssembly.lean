module

public import AFree.Paper.DivWaveCone
public import AFree.Paper.Augmented
public import AFree.Paper.AugmentedMeasure

/-!
# Corollary 1.13: conditional assembly

[DPR, Remark 1.3] (right-hand side reduced to the augmented operator) and the proof of
[DPR, Corollary 1.13] from the main theorem, which is taken as a hypothesis.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- The conclusion of the main theorem for the augmented measure
`μ̃ = (μ, σ)` gives the conclusion for `μ`. -/
theorem ae_polar_mem_waveCone_of_augmented {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Fin d → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (σ : VectorMeasure (Vec d) (κ → ℝ))
    (h : ∀ᵐ x ∂(euclideanVariation (augmentedMeasure μ σ)).singularPart volume,
      polar (augmentedMeasure μ σ) x ∈ waveConeFirstOrder (augmentedCoeff A)) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveConeFirstOrder A := by
  have h1 := ae_singularPart_of_le (euclideanVariation_le_augmentedMeasure_left μ σ) h
  have h2 := polar_augmentedMeasure_inl_proportional μ σ
  have h3 : ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, ∃ c : ℝ, 0 < c ∧
      (fun i => polar (augmentedMeasure μ σ) x (Sum.inl i)) = c • polar μ x :=
    Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ _) h2
  filter_upwards [h1, h3] with x hx ⟨c, hc, hxc⟩
  rw [mem_waveConeFirstOrder_augmentedCoeff_iff, hxc] at hx
  have := smul_mem_waveConeFirstOrder A hx c⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this

/-- The identity `𝒜μ = σ` in `𝒟'(Ω)` makes `μ̃ = (μ, σ)` free for
the augmented operator `Ã(P, Q) = 𝒜P - Q`. -/
theorem isFirstOrderFree_augmented_of_rhs {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (Ω : Set (Vec d)) (A : Fin d → Matrix κ ι ℝ) (A₀ : Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (σ : VectorMeasure (Vec d) (κ → ℝ))
    (h : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
      A₀ *ᵥ (∫ᵛ x, φ x ∂•μ) - (∫ᵛ x, φ x ∂•σ) =
        ∑ ℓ, A ℓ *ᵥ (∫ᵛ x, euclideanCoordDeriv ℓ φ x ∂•μ)) :
    IsFirstOrderFree Ω (augmentedCoeff A) (augmentedZeroth A₀) (augmentedMeasure μ σ) := by
  intro φ hφ
  have hψ : ∀ m, IsTestFunctionOn Ω (euclideanCoordDeriv m φ) := fun m =>
    ⟨contDiff_euclideanCoordDeriv hφ.1 m, hasCompactSupport_euclideanCoordDeriv hφ.2.1 m,
      (tsupport_euclideanCoordDeriv_subset_tsupport m φ).trans hφ.2.2⟩
  rw [augmentedZeroth_mulVec, integral_augmentedMeasure_of_isTestFunctionOn μ σ hφ]
  simp only [augmentedCoeff_mulVec, integral_augmentedMeasure_of_isTestFunctionOn μ σ (hψ _),
    Sum.elim_inl, Sum.elim_inr]
  exact h φ hφ

/-- [DPR, Corollary 1.13], conditional: the rank bound `rank_polar_le_of_div_eq`, with the
main theorem (order one, `ι = (Fin d × Fin d) ⊕ Fin d`, `κ = Fin d`) as hypothesis `hmainThm`. -/
theorem rank_polar_le_of_div_eq_of_main
    (hmainThm : ∀ {d : ℕ} (Ω : Set (Vec d)), IsOpen Ω →
      ∀ (A : Fin d → Matrix (Fin d) ((Fin d × Fin d) ⊕ Fin d) ℝ)
        (A₀ : Matrix (Fin d) ((Fin d × Fin d) ⊕ Fin d) ℝ)
        (μ : VectorMeasure (Vec d) (((Fin d × Fin d) ⊕ Fin d) → ℝ)),
        euclideanVariation μ Ωᶜ = 0 → IsFirstOrderFree Ω A A₀ μ →
        ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveConeFirstOrder A)
    {d : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (μ : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (σ : VectorMeasure (Vec d) (Vec d)) (hσ : euclideanVariation σ Ωᶜ = 0)
    (hdiv : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∀ k,
      -∑ j, (∫ᵛ x, euclideanCoordDeriv j φ x ∂•μ) (k, j) = (∫ᵛ x, φ x ∂•σ) k) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume,
      (Matrix.of fun k j => polar μ x (k, j)).rank ≤ d - 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (Matrix.rank_le_card_height _).trans (by simp)
  have hfree : IsFirstOrderFree Ω (augmentedCoeff (divCoeff d))
      (augmentedZeroth (0 : Matrix (Fin d) (Fin d × Fin d) ℝ)) (augmentedMeasure μ σ) := by
    refine isFirstOrderFree_augmented_of_rhs Ω _ _ μ σ fun φ hφ => ?_
    have hsum : ∀ w : Fin d → (Fin d × Fin d → ℝ),
        ∑ ℓ, divCoeff d ℓ *ᵥ w ℓ = fun k => ∑ ℓ, w ℓ (k, ℓ) := by
      intro w
      funext k
      simp [Matrix.mulVec, dotProduct, divCoeff, Fintype.sum_prod_type, ite_and,
        Finset.sum_ite_eq']
    rw [Matrix.zero_mulVec, hsum]
    funext k
    have := hdiv φ hφ k
    simp only [Pi.sub_apply, Pi.zero_apply]
    linarith
  have hmain := hmainThm Ω hΩ _ _ (augmentedMeasure μ σ)
    (euclideanVariation_augmentedMeasure_compl_eq_zero μ σ hμ hσ) hfree
  filter_upwards [ae_polar_mem_waveCone_of_augmented (divCoeff d) μ σ hmain] with x hx
  exact (mem_waveConeFirstOrder_divCoeff_iff hd _).1 hx

end AFree
