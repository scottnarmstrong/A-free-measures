module

public import AFree.Measure.VectorIntegral

/-!
# Polar facts: the singular part, restriction and the polar decomposition

* `AFree.euclideanVariation_restrict`: the variation of a restriction is the restriction.
* `AFree.euclideanVariation_lebesgueSingularPart`, `AFree.polar_lebesgueSingularPart_ae`: the variation and the polar of the singular part.
* `AFree.singularPart_mono`: monotonicity of the singular part.
* `AFree.piEuclideanNorm_polar_eq_one`: `|dμ/d|μ|| = 1` a.e.
-/

public section

open MeasureTheory Filter Topology

namespace AFree

open PDE

variable {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]

/-- Local form of `euclideanVariation_le_of_forall`: only subsets of `s` are tested. -/
theorem euclideanVariation_apply_le_of_forall (μ : VectorMeasure X (ι → ℝ)) {m : Measure X}
    {s : Set X} (hs : MeasurableSet s)
    (h : ∀ E, E ⊆ s → MeasurableSet E → ENNReal.ofReal (piEuclideanNorm (μ E)) ≤ m E) :
    euclideanVariation μ s ≤ m s := by
  simp only [euclideanVariation, preVariation_apply, VectorMeasure.ennrealToMeasure_apply hs,
    ennrealPreVariation_apply, preVariationFun, hs, dite_true, iSup_le_iff]
  intro i
  calc
    ∑ x ∈ i.parts, ENNReal.ofReal (piEuclideanNorm (μ x)) ≤ ∑ x ∈ i.parts, m x :=
        Finset.sum_le_sum fun t ht => h t (Subtype.coe_le_coe.mpr (i.le ht)) t.property
    _ = m (i.parts.sup Subtype.val) := by
      rw [Finset.sup_set_eq_biUnion]
      refine (measure_biUnion_finset ?_ fun b _ => b.property).symm
      intro a ha b hb hab
      simpa [disjoint_iff, Subtype.ext_iff] using i.disjoint ha hb hab
    _ ≤ m s := by
      rw [Finset.sup_set_eq_biUnion]
      exact measure_mono <| Set.iUnion₂_subset fun _ hp => Subtype.coe_le_coe.mpr (i.le hp)

/-- The variation of a restriction is the restriction of the variation. -/
theorem euclideanVariation_restrict (μ : VectorMeasure X (ι → ℝ)) {N : Set X}
    (hN : MeasurableSet N) :
    euclideanVariation (μ.restrict N) = (euclideanVariation μ).restrict N := by
  refine le_antisymm (euclideanVariation_le_of_forall _ fun E hE => ?_) ?_
  · rw [VectorMeasure.restrict_apply _ hN hE, Measure.restrict_apply hE]
    exact ofReal_piEuclideanNorm_le_euclideanVariation μ _
  · refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.restrict_apply hs]
    calc euclideanVariation μ (s ∩ N) ≤ euclideanVariation (μ.restrict N) (s ∩ N) := by
          refine euclideanVariation_apply_le_of_forall μ (hs.inter hN) fun E hEs hE => ?_
          have : (μ.restrict N) E = μ E := VectorMeasure.restrict_eq_self _ hN hE
            (hEs.trans Set.inter_subset_right)
          rw [← this]
          exact ofReal_piEuclideanNorm_le_euclideanVariation _ E
      _ ≤ _ := measure_mono Set.inter_subset_left

/-- The polar of a restriction agrees a.e. with the polar. -/
theorem polar_restrict_ae (μ : VectorMeasure X (ι → ℝ)) {N : Set X} (hN : MeasurableSet N) :
    polar (μ.restrict N) =ᵐ[euclideanVariation (μ.restrict N)] polar μ := by
  have hv := euclideanVariation_restrict μ hN
  have key : ∀ i, (fun x => polar (μ.restrict N) x i) =ᵐ[euclideanVariation (μ.restrict N)]
      fun x => polar μ x i := by
    intro i
    have hint : Integrable (fun x => polar μ x i) (euclideanVariation (μ.restrict N)) := by
      rw [hv]; exact (integrable_polar_apply μ i).restrict
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => (integrable_polar_apply _ i).integrableOn) (fun s _ _ => hint.integrableOn)
      fun s hs _ => ?_
    rw [← coordMeasure_eq_setIntegral _ i hs, coordMeasure_apply,
      VectorMeasure.restrict_apply _ hN hs, ← coordMeasure_apply,
      coordMeasure_eq_setIntegral μ i (hs.inter hN), hv, Measure.restrict_restrict hs]
  filter_upwards [ae_all_iff.2 key] with x hx
  funext i
  exact hx i

variable {d : ℕ}

/-- A Lebesgue-null measurable set off which a finite measure is absolutely continuous. -/
theorem exists_null_restrict_compl_ac (ν : Measure (Vec d)) [IsFiniteMeasure ν] :
    ∃ N : Set (Vec d), MeasurableSet N ∧ volume N = 0 ∧ ν.restrict Nᶜ ≪ volume := by
  obtain ⟨S, hS, h1, h2⟩ := Measure.mutuallySingular_singularPart ν (volume : Measure (Vec d))
  refine ⟨Sᶜ, hS.compl, h2, ?_⟩
  intro E hE
  rw [compl_compl, Measure.restrict_apply' hS]
  have hdec := Measure.singularPart_add_rnDeriv ν (volume : Measure (Vec d))
  have h3 : (volume.withDensity (ν.rnDeriv volume)) E = 0 :=
    withDensity_absolutelyContinuous _ _ hE
  rw [← hdec, Measure.add_apply]
  have h4 : ν.singularPart volume (E ∩ S) = 0 :=
    measure_mono_null Set.inter_subset_right h1
  rw [h4, zero_add]
  exact measure_mono_null Set.inter_subset_left h3

/-- If `N` is a measurable Lebesgue-null set off which `ν` is absolutely continuous, then the
singular part of `ν` is `ν` restricted to `N`. -/
theorem singularPart_eq_restrict (ν : Measure (Vec d)) [IsFiniteMeasure ν] {N : Set (Vec d)}
    (hN : MeasurableSet N) (h0 : volume N = 0) (hac : ν.restrict Nᶜ ≪ volume) :
    ν.singularPart volume = ν.restrict N := by
  symm
  refine Measure.eq_singularPart (Measure.measurable_rnDeriv (ν.restrict Nᶜ) volume) ⟨Nᶜ, hN.compl, ?_, ?_⟩ ?_
  · rw [Measure.restrict_apply hN.compl, Set.compl_inter_self, measure_empty]
  · simpa using h0
  · rw [Measure.withDensity_rnDeriv_eq _ _ hac, Measure.restrict_add_restrict_compl hN]

/-- For finite measures `ν₁ ≤ ν₂`, the singular parts are
ordered. -/
theorem singularPart_mono {ν₁ ν₂ : Measure (Vec d)} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h : ν₁ ≤ ν₂) : ν₁.singularPart volume ≤ ν₂.singularPart volume := by
  obtain ⟨N₁, h1, h10, h1ac⟩ := exists_null_restrict_compl_ac ν₁
  obtain ⟨N₂, h2, h20, h2ac⟩ := exists_null_restrict_compl_ac ν₂
  have hN : MeasurableSet (N₁ ∪ N₂) := h1.union h2
  have hN0 : volume (N₁ ∪ N₂) = 0 := measure_union_null h10 h20
  have e1 : ν₁.singularPart volume = ν₁.restrict (N₁ ∪ N₂) :=
    singularPart_eq_restrict ν₁ hN hN0 fun E hE => nonpos_iff_eq_zero.1
      (le_trans (Measure.restrict_mono (s := (N₁ ∪ N₂)ᶜ) (s' := N₁ᶜ)
        (Set.compl_subset_compl.2 Set.subset_union_left) le_rfl E) (h1ac hE).le)
  have e2 : ν₂.singularPart volume = ν₂.restrict (N₁ ∪ N₂) :=
    singularPart_eq_restrict ν₂ hN hN0 fun E hE => nonpos_iff_eq_zero.1
      (le_trans (Measure.restrict_mono (s := (N₁ ∪ N₂)ᶜ) (s' := N₂ᶜ)
        (Set.compl_subset_compl.2 Set.subset_union_right) le_rfl E) (h2ac hE).le)
  rw [e1, e2]
  exact Measure.restrict_mono_measure h _

/-- A property holding `ν₂.singularPart volume`-a.e. holds
`ν₁.singularPart volume`-a.e. -/
theorem ae_singularPart_of_le {ν₁ ν₂ : Measure (Vec d)} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] (h : ν₁ ≤ ν₂) {p : Vec d → Prop}
    (hp : ∀ᵐ x ∂(ν₂.singularPart volume), p x) : ∀ᵐ x ∂(ν₁.singularPart volume), p x :=
  Measure.absolutelyContinuous_of_le (singularPart_mono h) hp

/-- The singular part of a vector measure is its restriction to a Lebesgue-null measurable set
off which `|μ|` is absolutely continuous. -/
theorem lebesgueSingularPart_eq_restrict {ι : Type*} [Fintype ι]
    (μ : VectorMeasure (Vec d) (ι → ℝ)) {N : Set (Vec d)} (hN : MeasurableSet N)
    (h0 : volume N = 0) (hac : (euclideanVariation μ).restrict Nᶜ ≪ volume) :
    lebesgueSingularPart μ = μ.restrict N := by
  refine VectorMeasure.ext fun E hE => ?_
  funext i
  have hs : (coordMeasure μ i).singularPart volume = (coordMeasure μ i).restrict N := by
    symm
    have hac' : (coordMeasure μ i).restrict Nᶜ ≪ᵥ
        (volume : Measure (Vec d)).toENNRealVectorMeasure := by
      intro F hF
      by_cases hm : MeasurableSet F
      · rw [Measure.toENNRealVectorMeasure_apply_measurable hm] at hF
        rw [VectorMeasure.restrict_apply _ hN.compl hm]
        have h1 := ofReal_piEuclideanNorm_le_euclideanVariation μ (F ∩ Nᶜ)
        have h2 : euclideanVariation μ (F ∩ Nᶜ) = 0 := by
          have := hac hF
          rwa [Measure.restrict_apply' hN.compl] at this
        rw [h2, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
        rw [coordMeasure_apply]
        exact abs_nonpos_iff.mp ((abs_apply_le_piEuclideanNorm _ i).trans h1)
      · exact VectorMeasure.not_measurable _ hm
    refine SignedMeasure.eq_singularPart _ (SignedMeasure.rnDeriv ((coordMeasure μ i).restrict Nᶜ) volume)
      ?_ ?_
    · refine VectorMeasure.MutuallySingular.mk Nᶜ hN.compl (fun t ht htm => ?_)
        (fun t ht htm => ?_)
      · have : t ∩ N = ∅ := Set.eq_empty_of_subset_empty fun x hx => ht hx.1 hx.2
        rw [VectorMeasure.restrict_apply _ hN htm, this, VectorMeasure.empty]
      · rw [Measure.toENNRealVectorMeasure_apply_measurable htm]
        exact measure_mono_null (by simpa using ht) h0
    · rw [SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hac']
      exact (VectorMeasure.restrict_add_restrict_compl hN).symm
  rw [show lebesgueSingularPart μ E i = (coordMeasure μ i).singularPart volume E from rfl, hs,
    VectorMeasure.restrict_apply _ hN hE, VectorMeasure.restrict_apply _ hN hE]
  rfl

/-- [corBV#singular-part-transfer] `|μˢ| = (|μ|)ˢ`. -/
theorem euclideanVariation_lebesgueSingularPart {ι : Type*} [Fintype ι]
    (μ : VectorMeasure (Vec d) (ι → ℝ)) :
    euclideanVariation (lebesgueSingularPart μ) =
      (euclideanVariation μ).singularPart volume := by
  obtain ⟨N, hN, h0, hac⟩ := exists_null_restrict_compl_ac (euclideanVariation μ)
  rw [lebesgueSingularPart_eq_restrict μ hN h0 hac, euclideanVariation_restrict μ hN,
    singularPart_eq_restrict _ hN h0 hac]

/-- [corBV#singular-part-transfer] The polar of `μˢ` agrees `|μˢ|`-a.e. with the polar of `μ`. -/
theorem polar_lebesgueSingularPart_ae {ι : Type*} [Fintype ι]
    (μ : VectorMeasure (Vec d) (ι → ℝ)) :
    polar (lebesgueSingularPart μ) =ᵐ[euclideanVariation (lebesgueSingularPart μ)] polar μ := by
  obtain ⟨N, hN, h0, hac⟩ := exists_null_restrict_compl_ac (euclideanVariation μ)
  rw [lebesgueSingularPart_eq_restrict μ hN h0 hac]
  exact polar_restrict_ae μ hN

/-! ### The polar has Euclidean norm one -/

theorem piEuclideanNorm_nonneg (v : ι → ℝ) : 0 ≤ piEuclideanNorm v := Real.sqrt_nonneg _

theorem continuous_piEuclideanNorm : Continuous (piEuclideanNorm (ι := ι)) := by
  unfold piEuclideanNorm
  fun_prop

theorem sum_mul_self_eq_sq (v : ι → ℝ) : ∑ i, v i * v i = piEuclideanNorm v ^ 2 := by
  unfold piEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg _)]

/-- Cauchy–Schwarz for `piEuclideanNorm`. -/
theorem sum_mul_le_piEuclideanNorm_mul (v w : ι → ℝ) :
    ∑ i, v i * w i ≤ piEuclideanNorm v * piEuclideanNorm w := by
  unfold piEuclideanNorm
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => mul_self_nonneg _)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by simpa only [sq] using Finset.sum_mul_sq_le_sq_mul_sq _ v w))

theorem piEuclideanNorm_smul (c : ℝ) (v : ι → ℝ) :
    piEuclideanNorm (c • v) = |c| * piEuclideanNorm v := by
  unfold piEuclideanNorm
  have : ∑ i, (c • v) i * (c • v) i = c ^ 2 * ∑ i, v i * v i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [smul_eq_mul]; ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem measurable_piEuclideanNorm_polar (μ : VectorMeasure X (ι → ℝ)) :
    Measurable fun x => piEuclideanNorm (polar μ x) :=
  continuous_piEuclideanNorm.measurable.comp (measurable_polar μ)

theorem integrable_piEuclideanNorm_polar (μ : VectorMeasure X (ι → ℝ)) :
    Integrable (fun x => piEuclideanNorm (polar μ x)) (euclideanVariation μ) := by
  refine Integrable.mono' (g := fun x => ∑ i, |polar μ x i|)
    (integrable_finsetSum _ fun i _ => (integrable_polar_apply μ i).abs)
    (measurable_piEuclideanNorm_polar μ).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (piEuclideanNorm_nonneg _)]
  exact piEuclideanNorm_le_sum_abs _

/-- `∑ᵢ vᵢ μ(E)ᵢ = ∫_E v · (dμ/d|μ|) d|μ|`. -/
theorem sum_mul_apply_eq_setIntegral (μ : VectorMeasure X (ι → ℝ)) (v : ι → ℝ) {E : Set X}
    (hE : MeasurableSet E) :
    ∑ i, v i * μ E i = ∫ x in E, ∑ i, v i * polar μ x i ∂euclideanVariation μ := by
  rw [integral_finsetSum _ fun i _ => ((integrable_polar_apply μ i).const_mul (v i)).restrict]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, ← coordMeasure_eq_setIntegral μ i hE, coordMeasure_apply]

theorem piEuclideanNorm_apply_le_real (μ : VectorMeasure X (ι → ℝ)) (E : Set X) :
    piEuclideanNorm (μ E) ≤ (euclideanVariation μ).real E :=
  ENNReal.toReal_mono (measure_ne_top _ _)  (by
    have := ofReal_piEuclideanNorm_le_euclideanVariation μ E
    exact this) |> fun h => by
      simpa [ENNReal.toReal_ofReal (piEuclideanNorm_nonneg _), Measure.real] using h

/-- `|μ(E)| ≤ ∫_E |dμ/d|μ|| d|μ|`. -/
theorem piEuclideanNorm_apply_le_setIntegral (μ : VectorMeasure X (ι → ℝ)) {E : Set X}
    (hE : MeasurableSet E) :
    piEuclideanNorm (μ E) ≤ ∫ x in E, piEuclideanNorm (polar μ x) ∂euclideanVariation μ := by
  set w := μ E with hw
  have h1 : piEuclideanNorm w ^ 2 = ∑ i, w i * μ E i := by
    rw [← sum_mul_self_eq_sq]
  have h2 : ∑ i, w i * μ E i =
      ∫ x in E, ∑ i, w i * polar μ x i ∂euclideanVariation μ :=
    sum_mul_apply_eq_setIntegral μ w hE
  have h3 : ∫ x in E, ∑ i, w i * polar μ x i ∂euclideanVariation μ ≤
      ∫ x in E, piEuclideanNorm w * piEuclideanNorm (polar μ x) ∂euclideanVariation μ := by
    refine setIntegral_mono_on ?_ ?_ hE fun x _ => sum_mul_le_piEuclideanNorm_mul _ _
    · exact (integrable_finsetSum _ fun i _ =>
        ((integrable_polar_apply μ i).const_mul (w i))).integrableOn
    · exact ((integrable_piEuclideanNorm_polar μ).const_mul _).integrableOn
  rw [integral_const_mul] at h3
  rcases (piEuclideanNorm_nonneg w).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact setIntegral_nonneg hE fun x _ => piEuclideanNorm_nonneg _
  · have : piEuclideanNorm w * piEuclideanNorm w ≤
        piEuclideanNorm w * ∫ x in E, piEuclideanNorm (polar μ x) ∂euclideanVariation μ := by
      calc _ = piEuclideanNorm w ^ 2 := by ring
        _ ≤ _ := by rw [h1, h2]; exact h3
    exact le_of_mul_le_mul_left this hpos

/-- `|μ| ≤ |dμ/d|μ|| · |μ|` as measures. -/
theorem euclideanVariation_le_withDensity_polar (μ : VectorMeasure X (ι → ℝ)) :
    euclideanVariation μ ≤
      (euclideanVariation μ).withDensity fun x => ENNReal.ofReal (piEuclideanNorm (polar μ x)) := by
  refine euclideanVariation_le_of_forall μ fun E hE => ?_
  rw [withDensity_apply _ hE,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_piEuclideanNorm_polar μ).integrableOn
      (Eventually.of_forall fun x => piEuclideanNorm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (piEuclideanNorm_apply_le_setIntegral μ hE)

theorem one_le_piEuclideanNorm_polar_ae (μ : VectorMeasure X (ι → ℝ)) :
    ∀ᵐ x ∂euclideanVariation μ, 1 ≤ piEuclideanNorm (polar μ x) := by
  have hf : Integrable (fun x => piEuclideanNorm (polar μ x) - 1) (euclideanVariation μ) :=
    (integrable_piEuclideanNorm_polar μ).sub (integrable_const _)
  have := ae_nonneg_of_forall_setIntegral_nonneg hf fun E hE _ => by
    rw [integral_sub (integrable_piEuclideanNorm_polar μ).integrableOn
      (integrable_const _ |>.integrableOn), setIntegral_const, smul_eq_mul, mul_one,
      sub_nonneg]
    have h := euclideanVariation_le_withDensity_polar μ E
    rw [withDensity_apply _ hE,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_piEuclideanNorm_polar μ).integrableOn
      (Eventually.of_forall fun x => piEuclideanNorm_nonneg _)] at h
    exact ENNReal.toReal_le_of_le_ofReal
      (setIntegral_nonneg hE fun x _ => piEuclideanNorm_nonneg _) h
  filter_upwards [this] with x hx
  simpa using hx

theorem sum_mul_polar_le_one_ae (μ : VectorMeasure X (ι → ℝ)) {v : ι → ℝ}
    (hv : piEuclideanNorm v = 1) :
    ∀ᵐ x ∂euclideanVariation μ, ∑ i, v i * polar μ x i ≤ 1 := by
  have hf : Integrable (fun x => 1 - ∑ i, v i * polar μ x i) (euclideanVariation μ) :=
    (integrable_const _).sub
      (integrable_finsetSum _ fun i _ => (integrable_polar_apply μ i).const_mul (v i))
  have := ae_nonneg_of_forall_setIntegral_nonneg hf fun E hE _ => by
    rw [integral_sub (integrable_const _ |>.integrableOn)
      (integrable_finsetSum _ fun i _ =>
        ((integrable_polar_apply μ i).const_mul (v i))).integrableOn,
      ← sum_mul_apply_eq_setIntegral μ v hE, setIntegral_const, smul_eq_mul, mul_one,
      sub_nonneg]
    calc ∑ i, v i * μ E i ≤ piEuclideanNorm v * piEuclideanNorm (μ E) :=
          sum_mul_le_piEuclideanNorm_mul _ _
      _ ≤ _ := by rw [hv, one_mul]; exact piEuclideanNorm_apply_le_real μ E
  filter_upwards [this] with x hx
  simpa using hx

/-- [corBV#nonzero-factors] The polar has Euclidean norm one `|μ|`-a.e. -/
theorem piEuclideanNorm_polar_eq_one (μ : VectorMeasure X (ι → ℝ)) :
    ∀ᵐ x ∂euclideanVariation μ, piEuclideanNorm (polar μ x) = 1 := by
  let S : Set (ι → ℝ) := {v | piEuclideanNorm v = 1}
  obtain ⟨t, ht, htS, hSt⟩ := TopologicalSpace.exists_countable_dense_subset S
  have hall : ∀ᵐ x ∂euclideanVariation μ, ∀ u : t, ∑ i, u.1 i * polar μ x i ≤ 1 := by
    have := ht.to_subtype
    rw [ae_all_iff]
    intro u
    exact sum_mul_polar_le_one_ae μ (htS u.2)
  filter_upwards [hall, one_le_piEuclideanNorm_polar_ae μ] with x hx hx1
  refine le_antisymm ?_ hx1
  set P := polar μ x
  have hP : 0 < piEuclideanNorm P := lt_of_lt_of_le one_pos hx1
  have hu : piEuclideanNorm ((piEuclideanNorm P)⁻¹ • P) = 1 := by
    rw [piEuclideanNorm_smul, abs_of_pos (inv_pos.2 hP), inv_mul_cancel₀ hP.ne']
  have hclosed : IsClosed {s : ι → ℝ | ∑ i, s i * P i ≤ 1} :=
    isClosed_le (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul continuous_const) continuous_const
  have hsub : t ⊆ {s : ι → ℝ | ∑ i, s i * P i ≤ 1} := fun s hs => hx ⟨s, hs⟩
  have hmem := hclosed.closure_subset_iff.2 hsub (hSt hu)
  have e : ∑ i, ((piEuclideanNorm P)⁻¹ • P) i * P i = piEuclideanNorm P := by
    have e : ∑ i, ((piEuclideanNorm P)⁻¹ • P) i * P i = (piEuclideanNorm P)⁻¹ * ∑ i, P i * P i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [smul_eq_mul]; ring
    rw [e, sum_mul_self_eq_sq]
    field_simp
  rw [← e]
  exact hmem

end AFree
