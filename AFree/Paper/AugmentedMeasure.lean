module

public import AFree.Measure.PolarFacts

/-!
# The augmented measure

For `μ` and `σ` on the same space, the measure `μ̃ = (μ, σ)` with values in `ℝ^{ι ⊕ κ}` used in
[DPR, Remark 1.3], and its basic properties.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {X : Type*} [MeasurableSpace X]

/-- The augmented measure `μ̃ = (μ, σ)`. -/
noncomputable def augmentedMeasure (μ : VectorMeasure X (ι → ℝ)) (σ : VectorMeasure X (κ → ℝ)) :
    VectorMeasure X (ι ⊕ κ → ℝ) where
  measureOf' s := Sum.elim (μ s) (σ s)
  empty' := by funext j; cases j <;> simp
  not_measurable' s hs := by
    funext j; cases j <;> simp [VectorMeasure.not_measurable _ hs]
  m_iUnion' f hf hdisj := by
    refine Pi.hasSum.2 fun j => ?_
    cases j with
    | inl i => exact Pi.hasSum.1 (VectorMeasure.m_iUnion μ hf hdisj) i
    | inr k => exact Pi.hasSum.1 (VectorMeasure.m_iUnion σ hf hdisj) k

omit [Fintype ι] [Fintype κ] in
/-- The `inl i` coordinate of `μ̃` is `μᵢ`. -/
theorem coordMeasure_augmentedMeasure_inl (μ : VectorMeasure X (ι → ℝ))
    (σ : VectorMeasure X (κ → ℝ)) (i : ι) :
    coordMeasure (augmentedMeasure μ σ) (Sum.inl i) = coordMeasure μ i :=
  VectorMeasure.ext fun _ _ => rfl

omit [Fintype ι] [Fintype κ] in
/-- The `inr k` coordinate of `μ̃` is `σₖ`. -/
theorem coordMeasure_augmentedMeasure_inr (μ : VectorMeasure X (ι → ℝ))
    (σ : VectorMeasure X (κ → ℝ)) (k : κ) :
    coordMeasure (augmentedMeasure μ σ) (Sum.inr k) = coordMeasure σ k :=
  VectorMeasure.ext fun _ _ => rfl

theorem sum_elim_mul_self (a : ι → ℝ) (b : κ → ℝ) :
    ∑ j, Sum.elim a b j * Sum.elim a b j = ∑ i, a i * a i + ∑ k, b k * b k := by
  rw [Fintype.sum_sum_type]; simp

theorem piEuclideanNorm_le_elim_left (a : ι → ℝ) (b : κ → ℝ) :
    piEuclideanNorm a ≤ piEuclideanNorm (Sum.elim a b) := by
  unfold piEuclideanNorm
  rw [sum_elim_mul_self]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right
    (Finset.sum_nonneg fun k _ => mul_self_nonneg _))

theorem piEuclideanNorm_le_elim_right (a : ι → ℝ) (b : κ → ℝ) :
    piEuclideanNorm b ≤ piEuclideanNorm (Sum.elim a b) := by
  unfold piEuclideanNorm
  rw [sum_elim_mul_self]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left
    (Finset.sum_nonneg fun k _ => mul_self_nonneg _))

theorem piEuclideanNorm_elim_le (a : ι → ℝ) (b : κ → ℝ) :
    piEuclideanNorm (Sum.elim a b) ≤ piEuclideanNorm a + piEuclideanNorm b := by
  have ha := piEuclideanNorm_nonneg a
  have hb := piEuclideanNorm_nonneg b
  unfold piEuclideanNorm at *
  rw [sum_elim_mul_self]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [add_sq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg _)]
  nlinarith [mul_nonneg ha hb]

/-- `|μ| ≤ |μ̃|`. -/
theorem euclideanVariation_le_augmentedMeasure_left (μ : VectorMeasure X (ι → ℝ))
    (σ : VectorMeasure X (κ → ℝ)) :
    euclideanVariation μ ≤ euclideanVariation (augmentedMeasure μ σ) :=
  euclideanVariation_le_of_forall μ fun E _ =>
    (ENNReal.ofReal_le_ofReal (piEuclideanNorm_le_elim_left _ _)).trans
      (ofReal_piEuclideanNorm_le_euclideanVariation (augmentedMeasure μ σ) E)

/-- `|σ| ≤ |μ̃|`. -/
theorem euclideanVariation_le_augmentedMeasure_right (μ : VectorMeasure X (ι → ℝ))
    (σ : VectorMeasure X (κ → ℝ)) :
    euclideanVariation σ ≤ euclideanVariation (augmentedMeasure μ σ) :=
  euclideanVariation_le_of_forall σ fun E _ =>
    (ENNReal.ofReal_le_ofReal (piEuclideanNorm_le_elim_right _ _)).trans
      (ofReal_piEuclideanNorm_le_euclideanVariation (augmentedMeasure μ σ) E)

/-- `|μ̃| ≤ |μ| + |σ|`. -/
theorem euclideanVariation_augmentedMeasure_le (μ : VectorMeasure X (ι → ℝ))
    (σ : VectorMeasure X (κ → ℝ)) :
    euclideanVariation (augmentedMeasure μ σ) ≤ euclideanVariation μ + euclideanVariation σ := by
  refine euclideanVariation_le_of_forall _ fun E _ => ?_
  rw [Measure.add_apply]
  calc ENNReal.ofReal (piEuclideanNorm (augmentedMeasure μ σ E))
      ≤ ENNReal.ofReal (piEuclideanNorm (μ E) + piEuclideanNorm (σ E)) :=
        ENNReal.ofReal_le_ofReal (piEuclideanNorm_elim_le _ _)
    _ ≤ ENNReal.ofReal (piEuclideanNorm (μ E)) + ENNReal.ofReal (piEuclideanNorm (σ E)) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add (ofReal_piEuclideanNorm_le_euclideanVariation μ E)
        (ofReal_piEuclideanNorm_le_euclideanVariation σ E)

/-- `|μ̃|(Ωᶜ) = 0` when `|μ|(Ωᶜ) = |σ|(Ωᶜ) = 0`. -/
theorem euclideanVariation_augmentedMeasure_compl_eq_zero (μ : VectorMeasure X (ι → ℝ))
    (σ : VectorMeasure X (κ → ℝ)) {Ω : Set X} (hμ : euclideanVariation μ Ωᶜ = 0)
    (hσ : euclideanVariation σ Ωᶜ = 0) :
    euclideanVariation (augmentedMeasure μ σ) Ωᶜ = 0 := by
  refine le_antisymm ?_ bot_le
  calc _ ≤ (euclideanVariation μ + euclideanVariation σ) Ωᶜ :=
        euclideanVariation_augmentedMeasure_le μ σ _
    _ = 0 := by rw [Measure.add_apply, hμ, hσ, add_zero]

/-! ### Polars of coordinates with a common coordinate measure -/

/-- If a coordinate of `ρ` equals a coordinate of `μ` and `|μ| ≤ |ρ|`, then the corresponding
polar coordinates differ by the factor `d|μ|/d|ρ|`, `|ρ|`-a.e. -/
theorem polar_apply_ae_eq_rnDeriv_mul {ι' : Type*} [Fintype ι'] (μ : VectorMeasure X (ι → ℝ))
    (ρ : VectorMeasure X (ι' → ℝ)) (i : ι) (j : ι') (hc : coordMeasure ρ j = coordMeasure μ i)
    (hle : euclideanVariation μ ≤ euclideanVariation ρ) :
    (fun x => polar ρ x j) =ᵐ[euclideanVariation ρ]
      fun x => ((euclideanVariation μ).rnDeriv (euclideanVariation ρ) x).toReal *
        polar μ x i := by
  have hac : euclideanVariation μ ≪ euclideanVariation ρ := Measure.absolutelyContinuous_of_le hle
  have hint : Integrable (fun x => ((euclideanVariation μ).rnDeriv (euclideanVariation ρ) x).toReal
      * polar μ x i) (euclideanVariation ρ) :=
    (integrable_toReal_rnDeriv_mul_iff hac).2 (integrable_polar_apply μ i)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ _ => (integrable_polar_apply ρ j).integrableOn) (fun s _ _ => hint.integrableOn)
    fun s hs _ => ?_
  rw [← coordMeasure_eq_setIntegral ρ j hs, hc, coordMeasure_eq_setIntegral μ i hs]
  simp_rw [← smul_eq_mul]
  exact (setIntegral_rnDeriv_smul hac hs).symm

/-- `polar μ̃` restricted to the first block is a positive multiple
of `polar μ`, `|μ|`-a.e. (with `c = d|μ|/d|μ̃|`). -/
theorem polar_augmentedMeasure_inl_proportional (μ : VectorMeasure X (ι → ℝ))
    (σ : VectorMeasure X (κ → ℝ)) :
    ∀ᵐ x ∂euclideanVariation μ, ∃ c : ℝ, 0 < c ∧
      (fun i => polar (augmentedMeasure μ σ) x (Sum.inl i)) = c • polar μ x := by
  have hle := euclideanVariation_le_augmentedMeasure_left μ σ
  have hac : euclideanVariation μ ≪ euclideanVariation (augmentedMeasure μ σ) :=
    Measure.absolutelyContinuous_of_le hle
  have h1 : ∀ i, ∀ᵐ x ∂euclideanVariation μ, polar (augmentedMeasure μ σ) x (Sum.inl i) =
      ((euclideanVariation μ).rnDeriv (euclideanVariation (augmentedMeasure μ σ)) x).toReal *
        polar μ x i := fun i =>
    hac.ae_le (polar_apply_ae_eq_rnDeriv_mul μ _ i (Sum.inl i)
      (coordMeasure_augmentedMeasure_inl μ σ i) hle)
  filter_upwards [ae_all_iff.2 h1, Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_lt_top (euclideanVariation μ)
      (euclideanVariation (augmentedMeasure μ σ)))] with x hx hpos hlt
  exact ⟨_, ENNReal.toReal_pos hpos.ne' hlt.ne, funext fun i => hx i⟩

/-! ### The vector integral against the augmented measure -/

/-- A coordinate of `∫ g dρ` only depends on the coordinate measure, if `|ν| ≤ |ρ|`. -/
theorem integral_apply_eq_of_coordMeasure_eq {ι' ι'' : Type*} [Fintype ι'] [Fintype ι'']
    (ν : VectorMeasure X (ι' → ℝ)) (ρ : VectorMeasure X (ι'' → ℝ)) (i : ι') (j : ι'')
    {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (hc : coordMeasure ρ j = coordMeasure ν i)
    (hle : euclideanVariation ν ≤ euclideanVariation ρ) :
    (∫ᵛ x, g x ∂•ρ) j = (∫ᵛ x, g x ∂•ν) i := by
  have hac : euclideanVariation ν ≪ euclideanVariation ρ := Measure.absolutelyContinuous_of_le hle
  rw [integral_smul_vectorMeasure_apply _ hg hC, integral_smul_vectorMeasure_apply _ hg hC]
  rw [integral_congr_ae (g := fun x =>
    ((euclideanVariation ν).rnDeriv (euclideanVariation ρ) x).toReal *
      (g x * polar ν x i))]
  · exact integral_toReal_rnDeriv_mul hac
  · filter_upwards [polar_apply_ae_eq_rnDeriv_mul ν ρ i j hc hle] with x hx
    rw [hx]; ring

/-- For bounded measurable `g`,
`∫ g dμ̃ = (∫ g dμ, ∫ g dσ)`. -/
theorem integral_augmentedMeasure (μ : VectorMeasure X (ι → ℝ)) (σ : VectorMeasure X (κ → ℝ))
    {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    ∫ᵛ x, g x ∂•(augmentedMeasure μ σ) =
      Sum.elim (∫ᵛ x, g x ∂•μ) (∫ᵛ x, g x ∂•σ) := by
  funext j
  cases j with
  | inl i =>
    rw [Sum.elim_inl]
    exact integral_apply_eq_of_coordMeasure_eq μ _ i (Sum.inl i) hg hC (coordMeasure_augmentedMeasure_inl μ σ i)
      (euclideanVariation_le_augmentedMeasure_left μ σ)
  | inr k =>
    rw [Sum.elim_inr]
    exact integral_apply_eq_of_coordMeasure_eq σ _ k (Sum.inr k) hg hC (coordMeasure_augmentedMeasure_inr μ σ k)
      (euclideanVariation_le_augmentedMeasure_right μ σ)

/-- The form needed for a test function `φ ∈ C_c^∞(Ω)`. -/
theorem integral_augmentedMeasure_of_isTestFunctionOn {d : ℕ} (μ : VectorMeasure (Vec d) (ι → ℝ))
    (σ : VectorMeasure (Vec d) (κ → ℝ)) {Ω : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsTestFunctionOn Ω φ) :
    ∫ᵛ x, φ x ∂•(augmentedMeasure μ σ) = Sum.elim (∫ᵛ x, φ x ∂•μ) (∫ᵛ x, φ x ∂•σ) := by
  have hcont : Continuous φ := hφ.1.continuous
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hφ.2.1
  exact integral_augmentedMeasure μ σ hcont.measurable hC

end AFree
