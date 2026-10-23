module

public import AFree.MetricCurrents.AKChain
public import AFree.MetricCurrents.MollMap
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Auxiliary facts for the density `ν`: the set function `B ↦ T(1_B, x)`
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.Nu

open PDE AFree

variable {d : ℕ} {T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ}

lemma coord_lip (i : Fin d) : IsEuclLipschitzWith 1 (coordTuple d i) := by
  intro x y
  have h := sq_apply_le_vecNormSq (x - y) i
  have h2 : |x i - y i| ≤ vecEuclideanNorm (x - y) := by
    unfold vecEuclideanNorm
    exact Real.abs_le_sqrt (by simpa using h)
  simpa [coordTuple] using h2

lemma coordTuple_lip : IsLipTuple (coordTuple d) := fun i => ⟨1, coord_lip i⟩

lemma isBorelBdd_indicator {B : Set (Vec d)} (hB : MeasurableSet B) :
    IsBorelBdd (B.indicator (1 : Vec d → ℝ)) := by
  refine ⟨measurable_one.indicator hB, 1, fun x => ?_⟩
  by_cases hx : x ∈ B <;> simp [hx]

lemma isBorelBdd_smul_add {h g : Vec d → ℝ} (hh : IsBorelBdd h) (hg : IsBorelBdd g) (a b : ℝ) :
    IsBorelBdd (a • h + b • g) := by
  obtain ⟨hm, C, hC⟩ := hh
  obtain ⟨gm, D, hD⟩ := hg
  refine ⟨(hm.const_smul a).add (gm.const_smul b), |a| * C + |b| * D, fun x => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |a * h x + b * g x| ≤ |a * h x| + |b * g x| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hD x) (abs_nonneg _))

lemma isBorelBdd_zero : IsBorelBdd (0 : Vec d → ℝ) := ⟨measurable_const, 0, fun x => by simp⟩

section ext
variable (hT : IsMetricCurrent d T)
include hT

lemma ext_add {h g : Vec d → ℝ} (hh : IsBorelBdd h) (hg : IsBorelBdd g) (a b : ℝ) :
    akExt T (a • h + b • g) (coordTuple d) = a * akExt T h (coordTuple d) +
      b * akExt T g (coordTuple d) :=
  (akext hT).1.2.1 _ coordTuple_lip h g hh hg a b

lemma ext_zero : akExt T (0 : Vec d → ℝ) (coordTuple d) = 0 := by
  have := ext_add hT isBorelBdd_zero isBorelBdd_zero 0 0
  simpa using this

lemma ext_bound {μ : Measure (Vec d)} (hμ : IsAKMassAdmissible T μ) {h : Vec d → ℝ}
    (hh : IsBorelBdd h) : |akExt T h (coordTuple d)| ≤ ∫ x, |h x| ∂μ := by
  have := (akext hT).1.2.2.2 μ hμ h hh (coordTuple d) (fun _ => 1) (fun i => coord_lip i)
  simpa using this

lemma ext_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (g : ι → Vec d → ℝ)
    (hg : ∀ i, IsBorelBdd (g i)) :
    akExt T (∑ i ∈ s, c i • g i) (coordTuple d) = ∑ i ∈ s, c i * akExt T (g i) (coordTuple d) ∧
      IsBorelBdd (∑ i ∈ s, c i • g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using ext_zero hT, by simpa using isBorelBdd_zero⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hb : IsBorelBdd (c a • g a + (1 : ℝ) • ∑ i ∈ s, c i • g i) :=
      isBorelBdd_smul_add (hg a) ih2 _ _
    refine ⟨?_, by simpa using hb⟩
    have := ext_add hT (hg a) ih2 (c a) 1
    simpa [ih1] using this

end ext

section construct
variable (hT : IsMetricCurrent d T)
include hT

lemma ext_union {A B : Set (Vec d)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) :
    akExt T ((A ∪ B).indicator 1) (coordTuple d) =
      akExt T (A.indicator 1) (coordTuple d) + akExt T (B.indicator 1) (coordTuple d) := by
  have h := ext_add hT (isBorelBdd_indicator hA) (isBorelBdd_indicator hB) 1 1
  have e : ((1 : ℝ) • A.indicator (1 : Vec d → ℝ) + (1 : ℝ) • B.indicator (1 : Vec d → ℝ)) =
      (A ∪ B).indicator 1 := by
    rw [Set.indicator_union_of_disjoint hAB]; ext x; simp
  rw [e] at h
  simpa using h

lemma ext_biUnion {f : ℕ → Set (Vec d)} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Function.onFun Disjoint f)) (n : ℕ) :
    akExt T ((⋃ i ∈ Finset.range n, f i).indicator 1) (coordTuple d) =
      ∑ i ∈ Finset.range n, akExt T ((f i).indicator 1) (coordTuple d) := by
  induction n with
  | zero =>
    have e : (⋃ i ∈ Finset.range 0, f i) = ∅ := by simp
    rw [e, Set.indicator_empty, Finset.sum_range_zero]
    exact ext_zero hT
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have e : (⋃ i ∈ Finset.range (n + 1), f i) = (⋃ i ∈ Finset.range n, f i) ∪ f n := by
      ext x; simp [Finset.mem_range]; grind
    rw [e]
    refine ext_union hT (Finset.measurableSet_biUnion _ fun i _ => hf i) (hf n) ?_
    rw [Set.disjoint_iUnion₂_left]
    intro i hi
    exact hd (by have := Finset.mem_range.1 hi; omega : i ≠ n)

lemma ext_indicator_bound {μ : Measure (Vec d)} (hμ : IsAKMassAdmissible T μ) {B : Set (Vec d)}
    (hB : MeasurableSet B) :
    |akExt T (B.indicator 1) (coordTuple d)| ≤ μ.real B := by
  have := ext_bound hT hμ (isBorelBdd_indicator hB)
  have e : ∫ x, |B.indicator (1 : Vec d → ℝ) x| ∂μ = μ.real B := by
    rw [← integral_indicator_one hB]
    congr 1; ext x; by_cases hx : x ∈ B <;> simp [hx]
  linarith

open Classical in
/-- The set function `B ↦ T(1_B, x)` as a signed measure. -/
noncomputable def nuMeasure : SignedMeasure (Vec d) where
  measureOf' B := if MeasurableSet B then akExt T (B.indicator 1) (coordTuple d) else 0
  empty' := by
    simp only [MeasurableSet.empty, ↓reduceIte, Set.indicator_empty]
    exact ext_zero hT
  not_measurable' B hB := by simp [hB]
  m_iUnion' f hf hd := by
    obtain ⟨μ, hμ⟩ : ∃ μ, IsAKMass T μ := ⟨akMassMeasure T, akMassMeasure_isAKMass hT⟩
    have : IsFiniteMeasure μ := hμ.1.1
    have hU : MeasurableSet (⋃ i, f i) := MeasurableSet.iUnion hf
    simp only [hf, hU, ite_true]
    have hs : Summable fun i => akExt T ((f i).indicator 1) (coordTuple d) :=
      Summable.of_norm_bounded (summable_measure_toReal hf hd)
        (fun i => ext_indicator_bound hT hμ.1 (hf i))
    refine (hs.hasSum_iff_tendsto_nat).2 ?_
    have hT0 : Tendsto (fun n => μ.real (⋃ i ∈ Set.Ici n, f i)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => μ (⋃ i ∈ Set.Ici n, f i)) atTop (𝓝 0) := by
        have := tendsto_measure_iInter_atTop (μ := μ) (s := fun n => ⋃ i ∈ Set.Ici n, f i)
          (fun n => (MeasurableSet.biUnion (Set.to_countable _) fun i _ => hf i).nullMeasurableSet)
          (fun a b hab => Set.biUnion_subset_biUnion_left (Set.Ici_subset_Ici.2 hab))
          ⟨0, measure_ne_top _ _⟩
        have e : (⋂ n, ⋃ i ∈ Set.Ici n, f i) = ∅ := by
          ext x
          simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_Ici, exists_prop, Set.mem_empty_iff_false,
            iff_false, not_forall, not_exists, not_and]
          by_contra hx
          push Not at hx
          obtain ⟨i, hi⟩ := hx 0
          obtain ⟨j, hj, hxj⟩ := hx (i + 1)
          exact (Set.disjoint_left.1 (hd (by omega : i ≠ j)) hi.2) hxj
        rw [e, measure_empty] at this
        exact this
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      simpa [Measure.real, Function.comp_def] using this
    have key : ∀ n, akExt T ((⋃ i, f i).indicator 1) (coordTuple d) -
        ∑ i ∈ Finset.range n, akExt T ((f i).indicator 1) (coordTuple d) =
        akExt T ((⋃ i ∈ Set.Ici n, f i).indicator 1) (coordTuple d) := by
      intro n
      have e : (⋃ i, f i) = (⋃ i ∈ Finset.range n, f i) ∪ (⋃ i ∈ Set.Ici n, f i) := by
        ext x; simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, Set.mem_union, Set.mem_Ici]
        constructor
        · rintro ⟨i, hi⟩
          by_cases h : i < n
          · exact Or.inl ⟨i, h, hi⟩
          · exact Or.inr ⟨i, by omega, hi⟩
        · rintro (⟨i, _, hi⟩ | ⟨i, _, hi⟩) <;> exact ⟨i, hi⟩
      have hdis : Disjoint (⋃ i ∈ Finset.range n, f i) (⋃ i ∈ Set.Ici n, f i) := by
        rw [Set.disjoint_iUnion₂_left]
        intro i hi
        rw [Set.disjoint_iUnion₂_right]
        intro j hj
        exact hd (by simp at hi hj; omega)
      rw [e, ext_union hT (Finset.measurableSet_biUnion _ fun i _ => hf i)
        (MeasurableSet.biUnion (Set.to_countable _) fun i _ => hf i) hdis,
        ext_biUnion hT hf hd n]
      ring
    refine tendsto_sub_nhds_zero_iff.1 ?_
    refine squeeze_zero_norm (fun n => ?_) hT0
    rw [norm_sub_rev, key n, Real.norm_eq_abs]
    exact ext_indicator_bound hT hμ.1 (MeasurableSet.biUnion (Set.to_countable _) fun i _ => hf i)

end construct

section integral

lemma abs_integral_le (ν : SignedMeasure (Vec d)) (g : Vec d → ℝ) :
    |∫ᵛ x, g x ∂•ν| ≤ ∫ x, |g x| ∂ν.variation := by
  have h := VectorMeasure.norm_integral_le_integral_norm (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := ν) (f := g)
  have h1 : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  calc |∫ᵛ x, g x ∂•ν| = ‖∫ᵛ x, g x ∂•ν‖ := (Real.norm_eq_abs _).symm
    _ ≤ _ := h
    _ ≤ 1 * ∫ x, ‖g x‖ ∂ν.variation :=
      mul_le_mul_of_nonneg_right h1 (integral_nonneg fun _ => norm_nonneg _)
    _ = _ := by simp [Real.norm_eq_abs]

lemma integrable_of_isBorelBdd {m : Measure (Vec d)} [IsFiniteMeasure m] {h : Vec d → ℝ}
    (hh : IsBorelBdd h) : Integrable h m := by
  obtain ⟨hm, C, hC⟩ := hh
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC x)

lemma L1_sum (ν : SignedMeasure (Vec d)) [IsFiniteMeasure ν.variation] {ι : Type*} (F : Finset ι)
    (c : ι → ℝ) (A : ι → Set (Vec d)) (hA : ∀ y, MeasurableSet (A y)) :
    ∫ᵛ x, ∑ y ∈ F, c y * (A y).indicator (1 : Vec d → ℝ) x ∂•ν = ∑ y ∈ F, c y * ν (A y) := by
  have hint : ∀ y ∈ F, ν.Integrable (fun x => c y * (A y).indicator (1 : Vec d → ℝ) x) := by
    intro y _
    exact ((integrable_const (1 : ℝ)).indicator (hA y)).const_mul (c y) |>.congr (by
      filter_upwards with x; by_cases hx : x ∈ A y <;> simp [hx])
  rw [VectorMeasure.integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : (fun x => c y * (A y).indicator (1 : Vec d → ℝ) x) =
      fun x => c y • (A y).indicator (fun _ : Vec d => (1 : ℝ)) x := by
    ext x; by_cases hx : x ∈ A y <;> simp [hx]
  rw [this, VectorMeasure.integral_fun_smul,
    VectorMeasure.integral_indicator_const (1 : ℝ) (hA y)]
  simp [smul_eq_mul]

end integral

section simple

lemma tendsto_l1 {m : Measure (Vec d)} [IsFiniteMeasure m] {s : ℕ → Vec d → ℝ} {h : Vec d → ℝ}
    (hs : ∀ n, IsBorelBdd (s n)) (hh : IsBorelBdd h) {C : ℝ} (hb : ∀ n x, |s n x - h x| ≤ C)
    (hlim : ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (h x))) :
    Tendsto (fun n => ∫ x, |s n x - h x| ∂m) atTop (𝓝 0) := by
  have := tendsto_integral_of_dominated_convergence (μ := m) (F := fun n x => |s n x - h x|)
    (f := fun _ => 0) (bound := fun _ => C)
    (fun n => (continuous_abs.measurable.comp ((hs n).1.sub hh.1)).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb n x)
    (Eventually.of_forall fun x => by
      simpa using ((hlim x).sub_const (h x)).abs)
  simpa using this

lemma simple_eq (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)}
    [IsFiniteMeasure ν.variation]
    (hν : ∀ B, MeasurableSet B → ν B = akExt T (B.indicator 1) (coordTuple d))
    (s : SimpleFunc (Vec d) ℝ) :
    ∫ᵛ x, s x ∂•ν = akExt T s (coordTuple d) := by
  have hpt : ∀ x, s x = ∑ y ∈ s.range, y * (s ⁻¹' {y}).indicator (1 : Vec d → ℝ) x := by
    intro x
    rw [Finset.sum_eq_single (s x)]
    · simp
    · intro y _ hy
      have : x ∉ s ⁻¹' {y} := fun hx => hy (Set.mem_singleton_iff.1 hx).symm
      simp [this]
    · intro h; exact absurd (s.mem_range_self x) h
  have hfun : (⇑s : Vec d → ℝ) =
      ∑ y ∈ s.range, y • (s ⁻¹' {y}).indicator (1 : Vec d → ℝ) := by
    funext x
    rw [hpt x]
    simp [Finset.sum_apply]
  have hA : ∀ y, MeasurableSet (s ⁻¹' {y}) := fun y => s.measurableSet_fiber y
  have h1 := ext_sum hT s.range (fun y => y) (fun y => (s ⁻¹' {y}).indicator (1 : Vec d → ℝ))
    (fun y => isBorelBdd_indicator (hA y))
  have h2 := L1_sum ν s.range (fun y => y) (fun y => s ⁻¹' {y}) hA
  have e : (fun x => s x) = fun x => ∑ y ∈ s.range, y * (s ⁻¹' {y}).indicator (1 : Vec d → ℝ) x :=
    funext hpt
  rw [e, h2]
  have : akExt T s (coordTuple d) = akExt T (∑ y ∈ s.range, y • (s ⁻¹' {y}).indicator (1 : Vec d → ℝ))
      (coordTuple d) := by rw [← hfun]
  rw [this, h1.1]
  exact Finset.sum_congr rfl fun y _ => by rw [hν _ (hA y)]

end simple

section main

variable (hT : IsMetricCurrent d T)
include hT

lemma variation_le_of_apply {ν : SignedMeasure (Vec d)}
    (hν : ∀ B, MeasurableSet B → ν B = akExt T (B.indicator 1) (coordTuple d))
    {μ : Measure (Vec d)} (hμ : IsAKMassAdmissible T μ) : ν.variation ≤ μ := by
  have := hμ.1
  refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
  rw [hν E hE, Real.enorm_eq_ofReal_abs]
  calc ENNReal.ofReal |akExt T (E.indicator 1) (coordTuple d)| ≤ ENNReal.ofReal (μ.real E) :=
        ENNReal.ofReal_le_ofReal (ext_indicator_bound hT hμ hE)
    _ = μ E := ENNReal.ofReal_toReal (measure_ne_top μ E)

lemma finite_variation_of_apply {ν : SignedMeasure (Vec d)}
    (hν : ∀ B, MeasurableSet B → ν B = akExt T (B.indicator 1) (coordTuple d)) :
    IsFiniteMeasure ν.variation := by
  have hμ := akMassMeasure_isAKMass hT
  have := hμ.1.1
  exact isFiniteMeasure_of_le (akMassMeasure T) (variation_le_of_apply hT hν hμ.1)

lemma isNu_of_apply {ν : SignedMeasure (Vec d)}
    (hν : ∀ B, MeasurableSet B → ν B = akExt T (B.indicator 1) (coordTuple d)) :
    ∀ h : Vec d → ℝ, IsBorelBdd h → ∫ᵛ x, h x ∂•ν = akExt T h (coordTuple d) := by
  intro h hh
  have := finite_variation_of_apply hT hν
  have hμ := akMassMeasure_isAKMass hT
  have := hμ.1.1
  obtain ⟨hm, C, hC⟩ := hh
  let s : ℕ → SimpleFunc (Vec d) ℝ := fun n => SimpleFunc.approxOn h hm Set.univ 0 (Set.mem_univ _) n
  have hsb : ∀ n x, |s n x| ≤ 2 * C := fun n x => by
    have := SimpleFunc.norm_approxOn_zero_le hm (Set.mem_univ (0 : ℝ)) x n
    have h2 := hC x
    simp only [Real.norm_eq_abs] at this
    simp only [s]
    linarith
  have hsB : ∀ n, IsBorelBdd (s n) := fun n => ⟨(s n).measurable, 2 * C, hsb n⟩
  have hlim : ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (h x)) := fun x =>
    SimpleFunc.tendsto_approxOn hm (Set.mem_univ (0 : ℝ)) (by simp)
  have hbd : ∀ n x, |s n x - h x| ≤ 3 * C := by
    intro n x
    have := hsb n x
    have h2 := hC x
    calc |s n x - h x| ≤ |s n x| + |h x| := abs_sub _ _
      _ ≤ 3 * C := by linarith
  have hh' : IsBorelBdd h := ⟨hm, C, hC⟩
  -- the two sides along the sequence
  have L1 : Tendsto (fun n => ∫ᵛ x, s n x ∂•ν) atTop (𝓝 (∫ᵛ x, h x ∂•ν)) := by
    have hl := tendsto_l1 (m := ν.variation) hsB hh' hbd hlim
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hl
    rw [Real.norm_eq_abs]
    have hsi : ν.Integrable (s n) := integrable_of_isBorelBdd (hsB n)
    have hhi : ν.Integrable h := integrable_of_isBorelBdd hh'
    have := abs_integral_le ν (fun x => s n x - h x)
    rwa [VectorMeasure.integral_fun_sub hsi hhi] at this
  have L2 := (akext hT).2.2.1 (akMassMeasure T) hμ (fun n => ⇑(s n)) h hsB hh'
    (tendsto_l1 (m := akMassMeasure T) hsB hh' hbd hlim) (coordTuple d) coordTuple_lip
  have e : ∀ n, ∫ᵛ x, s n x ∂•ν = akExt T (s n) (coordTuple d) := fun n =>
    simple_eq hT hν (s n)
  simp only [e] at L1
  exact tendsto_nhds_unique L1 L2

end main

section lipschitz

lemma exists_lipschitzWith_of_eucl {K : ℝ≥0} {F : Vec d → ℝ} (hF : IsEuclLipschitzWith K F) :
    ∃ L : ℝ≥0, LipschitzWith L F := by
  refine ⟨K * (Real.sqrt d).toNNReal, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  calc |F x - F y| ≤ K * vecEuclideanNorm (x - y) := hF x y
    _ ≤ K * (Real.sqrt d * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (vecEuclideanNorm_le_sqrt_natCast_mul_norm _) K.2
    _ = _ := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]; ring

lemma isBorelBdd_of_isBddLipFun {f : Vec d → ℝ} (hf : IsBddLipFun f) : IsBorelBdd f := by
  obtain ⟨⟨K, hK⟩, C, hC⟩ := hf
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_eucl hK
  exact ⟨hL.continuous.measurable, C, hC⟩

lemma finite_variation (ν : SignedMeasure (Vec d)) : IsFiniteMeasure ν.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]; infer_instance

lemma isEucl_mono {K K' : ℝ≥0} {F : Vec d → ℝ} (h : K ≤ K') (hF : IsEuclLipschitzWith K F) :
    IsEuclLipschitzWith K' F := fun x y =>
  (hF x y).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast h) (vecEuclideanNorm_nonneg _))

end lipschitz

lemma nuMeasure_apply (hT : IsMetricCurrent d T) {B : Set (Vec d)} (hB : MeasurableSet B) :
    nuMeasure hT B = akExt T (B.indicator 1) (coordTuple d) := by
  classical
  show (if MeasurableSet B then _ else 0) = _
  simp [hB]

end AFree.MetricCurrents.Nu
