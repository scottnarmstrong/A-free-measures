module

public import AFree.Curves.Dichotomy.CurveMeasLambda

/-!
# `Λ_γ(U) ≤ 𝓗¹(U ∩ γ[0,1])` (the `≥` half of the length formula)
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

lemma injOn_ccurveExt {γ : C(I, Vec d)} (hγ : Function.Injective γ) :
    InjOn (ccurveExt γ) (Icc (0 : ℝ) 1) := fun x hx y hy h => by
  rw [ccurveExt_of_mem γ hx, ccurveExt_of_mem γ hy] at h
  exact congrArg Subtype.val (hγ h)

lemma ccurveExt_image_Ico_eq {γ : C(I, Vec d)} (hγ : Function.Injective γ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    ccurveExt γ '' Ico a b = ccurveExt γ '' Icc a b \ {ccurveExt γ b} := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha hb
  have := (injOn_ccurveExt hγ).mono hsub |>.image_sdiff_subset (t := {b})
    (singleton_subset_iff.2 ⟨hab, le_rfl⟩)
  rw [Icc_sdiff_right, image_singleton] at this
  exact this

/-- The chord of a counted interval is at most `𝓗¹` of the half-open image. -/
lemma ofReal_chord_le_Ico {γ : C(I, Vec d)} {a b : ℝ}
    (hab : a ≤ b) (hlip : LipschitzWith 1 (ccurveExt γ)) :
    ENNReal.ofReal (vecEuclideanNorm (ccurveExt γ b - ccurveExt γ a)) ≤
      euclideanHausdorffOne d (ccurveExt γ '' Ico a b) := by
  refine (ofReal_norm_sub_le_hausdorffOne hab hlip.continuous.continuousOn).trans ?_
  rw [← Ico_union_right hab, image_union, image_singleton]
  refine (measure_union_le _ _).trans ?_
  rw [euclideanHausdorffOne_singleton, add_zero]

lemma measurableSet_ccurveExt_image_Ico {γ : C(I, Vec d)} (hγ : Function.Injective γ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    MeasurableSet (ccurveExt γ '' Ico a b) := by
  rcases le_or_gt a b with hab | hab
  · rw [ccurveExt_image_Ico_eq hγ ha hb hab]
    have hc : Continuous (ccurveExt γ) := by
      have : ccurveExt γ = fun x => γ (Set.projIcc (0 : ℝ) 1 zero_le_one x) := rfl
      rw [this]
      exact γ.continuous.comp continuous_projIcc
    exact ((isCompact_Icc.image hc).measurableSet).diff (measurableSet_singleton _)
  · rw [Ico_eq_empty_of_le hab.le, image_empty]
    exact MeasurableSet.empty

lemma disjoint_Ico_of_le {a b c d' : ℝ} (h : b ≤ c) : Disjoint (Ico a b) (Ico c d') :=
  Set.disjoint_left.2 fun _ hx hy => absurd (hx.2.trans_le h) (not_lt.2 hy.1)

/-- (`≥` half) For `γ ∈ 𝒢(C)` and any `U`,
`Λ_γ(U) ≤ 𝓗¹(U ∩ γ([0,1]))`. -/
theorem curveLambda_le {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpace e α) (U : Set (Vec d)) :
    curveLambda γ U (Icc 0 1) ≤ euclideanHausdorffOne d (U ∩ range γ) := by
  obtain ⟨hinj, -, -, -, -⟩ := ccurveSpace_curve_properties hα hα2 hγ
  have hlip := lipschitzWith_ccurveExt hγ
  refine iSup_le fun ⟨n, u, hum, hu⟩ => ?_
  classical
  set T : ℕ → Set (Vec d) := fun i => ccurveExt γ '' Ico (u i) (u (i + 1)) with hT
  set S := (Finset.range n).filter fun i => ccurveExt γ '' Icc (u i) (u (i + 1)) ⊆ U with hS
  have hsubI : ∀ i, Ico (u i) (u (i + 1)) ⊆ Icc (0 : ℝ) 1 := fun i =>
    Ico_subset_Icc_self.trans (Icc_subset_Icc (hu i).1 (hu (i + 1)).2)
  have hmeas : ∀ i ∈ S, MeasurableSet (T i) := fun i _ =>
    measurableSet_ccurveExt_image_Ico hinj (hu i).1 (hu (i + 1)).2
  have hdisj : PairwiseDisjoint (↑S) T := by
    have key : ∀ i j, i < j → Disjoint (T i) (T j) := fun i j h =>
      Disjoint.image (disjoint_Ico_of_le (hum (Nat.succ_le_of_lt h))) (injOn_ccurveExt hinj)
        (hsubI i) (hsubI j)
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  have hsub : (⋃ i ∈ S, T i) ⊆ U ∩ range γ := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨i, hi, s, hs, rfl⟩ := hx
    have hiS := (Finset.mem_filter.1 hi).2
    refine ⟨hiS ⟨s, Ico_subset_Icc_self hs, rfl⟩, ?_⟩
    have hs01 := hsubI i hs
    exact ⟨⟨s, hs01⟩, (ccurveExt_of_mem γ hs01).symm⟩
  calc ∑ i ∈ Finset.range n, curveGap γ U (u i) (u (i + 1))
      ≤ ∑ i ∈ Finset.range n, if ccurveExt γ '' Icc (u i) (u (i + 1)) ⊆ U then
          euclideanHausdorffOne d (T i) else 0 := by
        refine Finset.sum_le_sum fun i hi => ?_
        unfold curveGap
        split_ifs
        · exact ofReal_chord_le_Ico (hum (Nat.le_succ i)) hlip
        · exact le_rfl
    _ = ∑ i ∈ S, euclideanHausdorffOne d (T i) := (Finset.sum_filter _ _).symm
    _ = euclideanHausdorffOne d (⋃ i ∈ S, T i) := (measure_biUnion_finset hdisj hmeas).symm
    _ ≤ _ := measure_mono hsub

end AFree
