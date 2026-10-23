module

public import AFree.Paper.AugmentedMeasure

/-!
# Block vector measures

For finitely many vector
measures `Tᵢ` with values in `ℝ^{κᵢ}`, the block measure `𝐓` has values in `ℝ^{Σᵢ κᵢ}`.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

variable {F : Type*} {κ : F → Type*} {X : Type*} [MeasurableSpace X]

/-- The block measure `𝐓(E)(⟨i, a⟩) = Tᵢ(E)(a)` with values in `ℝ^{Σᵢ κᵢ}`. -/
noncomputable def blockMeasure (T : ∀ i, VectorMeasure X (κ i → ℝ)) :
    VectorMeasure X ((Σ i, κ i) → ℝ) where
  measureOf' s := fun p => T p.1 s p.2
  empty' := by funext p; simp
  not_measurable' s hs := by funext p; simp [VectorMeasure.not_measurable _ hs]
  m_iUnion' f hf hdisj :=
    Pi.hasSum.2 fun p => Pi.hasSum.1 (VectorMeasure.m_iUnion (T p.1) hf hdisj) p.2

variable [Fintype F] [∀ i, Fintype (κ i)]

omit [Fintype F] [∀ i, Fintype (κ i)] in
/-- `𝐓_{⟨i,a⟩} = (Tᵢ)_a` as signed measures. -/
theorem coordMeasure_blockMeasure (T : ∀ i, VectorMeasure X (κ i → ℝ)) (i : F) (a : κ i) :
    coordMeasure (blockMeasure T) ⟨i, a⟩ = coordMeasure (T i) a :=
  VectorMeasure.ext fun _ _ => rfl

/-- Pointwise: `|v_i| ≤ |v|`. -/
theorem piEuclideanNorm_block_le (v : (Σ i, κ i) → ℝ) (i : F) :
    piEuclideanNorm (fun a => v ⟨i, a⟩) ≤ piEuclideanNorm v := by
  unfold piEuclideanNorm
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_sigma]
  exact Finset.single_le_sum (f := fun j => ∑ a, v ⟨j, a⟩ * v ⟨j, a⟩)
    (fun j _ => Finset.sum_nonneg fun a _ => mul_self_nonneg _) (Finset.mem_univ i)

/-- Pointwise: `|v| ≤ Σᵢ |v_i|`. -/
theorem piEuclideanNorm_le_sum_block (v : (Σ i, κ i) → ℝ) :
    piEuclideanNorm v ≤ ∑ i, piEuclideanNorm (fun a => v ⟨i, a⟩) := by
  unfold piEuclideanNorm
  rw [Fintype.sum_sigma]
  calc Real.sqrt (∑ i, ∑ a, v ⟨i, a⟩ * v ⟨i, a⟩)
      = Real.sqrt (∑ i, Real.sqrt (∑ a, v ⟨i, a⟩ * v ⟨i, a⟩) ^ 2) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.sq_sqrt (Finset.sum_nonneg fun a _ => mul_self_nonneg _)]
    _ ≤ Real.sqrt ((∑ i, Real.sqrt (∑ a, v ⟨i, a⟩ * v ⟨i, a⟩)) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Real.sqrt_nonneg _)
    _ = _ := Real.sqrt_sq (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _)

/-- `|Tᵢ| ≤ |𝐓|`. -/
theorem euclideanVariation_le_blockMeasure (T : ∀ i, VectorMeasure X (κ i → ℝ)) (i : F) :
    euclideanVariation (T i) ≤ euclideanVariation (blockMeasure T) :=
  euclideanVariation_le_of_forall _ fun E _ =>
    (ENNReal.ofReal_le_ofReal (piEuclideanNorm_block_le (blockMeasure T E) i)).trans
      (ofReal_piEuclideanNorm_le_euclideanVariation (blockMeasure T) E)

/-- `|𝐓| ≤ Σᵢ |Tᵢ|`. -/
theorem euclideanVariation_blockMeasure_le (T : ∀ i, VectorMeasure X (κ i → ℝ)) :
    euclideanVariation (blockMeasure T) ≤ ∑ i, euclideanVariation (T i) := by
  refine euclideanVariation_le_of_forall _ fun E _ => ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  calc ENNReal.ofReal (piEuclideanNorm (blockMeasure T E))
      ≤ ENNReal.ofReal (∑ i, piEuclideanNorm (T i E)) :=
        ENNReal.ofReal_le_ofReal (piEuclideanNorm_le_sum_block (blockMeasure T E))
    _ = ∑ i, ENNReal.ofReal (piEuclideanNorm (T i E)) :=
        ENNReal.ofReal_sum_of_nonneg fun i _ => piEuclideanNorm_nonneg _
    _ ≤ _ := Finset.sum_le_sum fun i _ => ofReal_piEuclideanNorm_le_euclideanVariation (T i) E

/-- `|𝐓|(E) = 0` if `|Tᵢ|(E) = 0` for all `i`. -/
theorem euclideanVariation_blockMeasure_eq_zero (T : ∀ i, VectorMeasure X (κ i → ℝ))
    {E : Set X} (hE : ∀ i, euclideanVariation (T i) E = 0) :
    euclideanVariation (blockMeasure T) E = 0 := by
  refine le_antisymm ((euclideanVariation_blockMeasure_le T E).trans ?_) bot_le
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp [hE]

/-- `|Tᵢ| ≪ |𝐓|`. -/
theorem euclideanVariation_absolutelyContinuous_blockMeasure (T : ∀ i, VectorMeasure X (κ i → ℝ))
    (i : F) : euclideanVariation (T i) ≪ euclideanVariation (blockMeasure T) :=
  Measure.absolutelyContinuous_of_le (euclideanVariation_le_blockMeasure T i)

/-- For bounded Borel `g`: `(∫ᵛ g d𝐓)⟨i,a⟩ = (∫ᵛ g dTᵢ)_a`. -/
theorem integral_blockMeasure_apply (T : ∀ i, VectorMeasure X (κ i → ℝ)) {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (i : F) (a : κ i) :
    (∫ᵛ x, g x ∂•(blockMeasure T)) ⟨i, a⟩ = (∫ᵛ x, g x ∂•(T i)) a :=
  integral_apply_eq_of_coordMeasure_eq (T i) (blockMeasure T) a ⟨i, a⟩ hg hC
    (coordMeasure_blockMeasure T i a) (euclideanVariation_le_blockMeasure T i)

/-- `(polar 𝐓)_i = c_i · polar Tᵢ` `|𝐓|`-a.e., for every `i`,
with `c_i = (d|Tᵢ|/d|𝐓|)_ℝ`. -/
theorem polar_blockMeasure_ae (T : ∀ i, VectorMeasure X (κ i → ℝ)) :
    ∀ᵐ x ∂euclideanVariation (blockMeasure T), ∀ i,
      (fun a => polar (blockMeasure T) x ⟨i, a⟩) =
        ((euclideanVariation (T i)).rnDeriv (euclideanVariation (blockMeasure T)) x).toReal •
          polar (T i) x := by
  rw [ae_all_iff]
  intro i
  have : ∀ a : κ i, ∀ᵐ x ∂euclideanVariation (blockMeasure T),
      polar (blockMeasure T) x ⟨i, a⟩ =
        ((euclideanVariation (T i)).rnDeriv (euclideanVariation (blockMeasure T)) x).toReal *
          polar (T i) x a := fun a =>
    polar_apply_ae_eq_rnDeriv_mul (T i) (blockMeasure T) a ⟨i, a⟩
      (coordMeasure_blockMeasure T i a) (euclideanVariation_le_blockMeasure T i)
  filter_upwards [ae_all_iff.2 this] with x hx
  funext a
  exact hx a

/-- `c_i > 0` `|Tᵢ|`-a.e. -/
theorem rnDeriv_blockMeasure_pos (T : ∀ i, VectorMeasure X (κ i → ℝ)) (i : F) :
    ∀ᵐ x ∂euclideanVariation (T i),
      0 < ((euclideanVariation (T i)).rnDeriv (euclideanVariation (blockMeasure T)) x).toReal := by
  have hac := euclideanVariation_absolutelyContinuous_blockMeasure T i
  filter_upwards [Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_lt_top (euclideanVariation (T i))
      (euclideanVariation (blockMeasure T)))] with x hpos hlt
  exact ENNReal.toReal_pos hpos.ne' hlt.ne

end AFree
