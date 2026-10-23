module

public import AFree.Curves.Dichotomy.CaseA
public import AFree.Curves.Dichotomy.CurveMeasMain

/-!
# The dichotomy, case B: the family `E_t` and its rectifiable-family clauses

Second case of the proof of [AM, Lemma 7.3]: the family `E_t` is a rectifiable family for `μ⌞F`.
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- `E_t = E₀ ∩ F ∩ ζ(t)([0,1])`, with `E₀ ⊆ B(k+1)` viewed in `ℝ^d`. -/
def dichFamily {e : Vec d} {α : ℝ} {k : ℕ} (F : Set (Vec d)) (E₀ : Set (curveBall d k))
    (ζ : I → ccurveSpaceK e α k) : I → Set (Vec d) :=
  fun t => Subtype.val '' E₀ ∩ F ∩ range ((ζ t : ccurveSpaceK e α k) : C(I, Vec d))

lemma dichFamily_subset {e : Vec d} {α : ℝ} {k : ℕ} (F : Set (Vec d)) (E₀ : Set (curveBall d k))
    (ζ : I → ccurveSpaceK e α k) (t : I) : dichFamily F E₀ ζ t ⊆ F := fun _ hx => hx.1.2

lemma measurableSet_image_val {k : ℕ} {E : Set (curveBall d k)} (hE : MeasurableSet E) :
    MeasurableSet (Subtype.val '' E : Set (Vec d)) :=
  (MeasurableEmbedding.subtype_coe (measurableSet_curveBall k)).measurableSet_image.2 hE

lemma measurableSet_dichFamily {e : Vec d} {α : ℝ} {k : ℕ} {F : Set (Vec d)}
    (hF : MeasurableSet F) {E₀ : Set (curveBall d k)} (hE₀ : MeasurableSet E₀)
    (ζ : I → ccurveSpaceK e α k) (t : I) : MeasurableSet (dichFamily F E₀ ζ t) :=
  ((measurableSet_image_val hE₀).inter hF).inter
    (isCompact_range (ζ t : C(I, Vec d)).continuous).isClosed.measurableSet

/-- Comparison of `𝓗¹(B ∩ γ[0,1])` and `λ_γ(B)` for `γ ∈ 𝒢_k`. -/
lemma hausdorff_le_law_and_law_le {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {k : ℕ} (γ : ccurveSpaceK e α k) {B : Set (Vec d)}
    (hB : MeasurableSet B) :
    euclideanHausdorffOne d (B ∩ range (γ : C(I, Vec d))) ≤
        (curveLawK e α k γ : Measure (curveBall d k)) (Subtype.val ⁻¹' B) ∧
      (curveLawK e α k γ : Measure (curveBall d k)) (Subtype.val ⁻¹' B) ≤
        ENNReal.ofReal (Real.cos α)⁻¹ * euclideanHausdorffOne d (B ∩ range (γ : C(I, Vec d))) := by
  have hcmp := (ccurveSpace_measure_comparison he hα hα2 (ccurveSpaceK_subset e α k γ.2)).2 B
  have hlaw : (curveLawK e α k γ : Measure (curveBall d k)) (Subtype.val ⁻¹' B) =
      volume ((γ : C(I, Vec d)) ⁻¹' B) := by
    rw [← curveLaw_apply _ hB, ← map_val_curveLawK, Measure.map_apply measurable_subtype_coe hB]
  rw [hlaw]
  exact hcmp

/-- Change of variables `∫ λ_{ζ(t)}(S) dt = [τ]_Φ(S)` for `ζ_# 𝓛¹ = τ`. -/
lemma lintegral_curveLawK_zeta {e : Vec d} {α : ℝ} {k : ℕ} (τ : ProbabilityMeasure (ccurveSpaceK e α k))
    {ζ : I → ccurveSpaceK e α k} (hζ : Measurable ζ) (hζτ : Measure.map ζ volume = (τ : Measure _))
    {S : Set (curveBall d k)} (hS : MeasurableSet S) :
    ∫⁻ t, (curveLawK e α k (ζ t) : Measure (curveBall d k)) S =
      mixMeasure (curveLawK e α k) (τ : Measure _) S := by
  have hΦ := continuous_curveLawK e α k
  rw [mixMeasure_apply hΦ _ hS, ← hζτ, lintegral_map _ hζ]
  exact (Measure.measurable_coe hS).comp (measurable_coe_of_continuous hΦ)

/-- Case B: for `τ ∈ 𝒫(𝒢_k)` and a Borel `E₀ ⊆ B(k+1)` with
`[τ]_Φ⌞E₀ ≪ μ_k`, and `ζ : [0,1] → 𝒢_k` Borel with `ζ_# 𝓛¹ = τ`, the family
`E_t = E₀ ∩ F ∩ ζ(t)([0,1])` satisfies `IsRectifiableFamily (μ.restrict F)`. -/
theorem dichotomy_family_construction {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ}
    (hα : 0 < α) (hα2 : α < Real.pi / 2) (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {F : Set (Vec d)} (hF : MeasurableSet F) {k : ℕ} (τ : ProbabilityMeasure (ccurveSpaceK e α k))
    {E₀ : Set (curveBall d k)} (hE₀ : MeasurableSet E₀)
    (hac : (mixMeasure (curveLawK e α k) (τ : Measure _)).restrict E₀ ≪ dichMeasure μ F k)
    {ζ : I → ccurveSpaceK e α k} (hζ : Measurable ζ) (hζτ : Measure.map ζ volume = (τ : Measure _)) :
    IsRectifiableFamily (μ.restrict F) (dichFamily F E₀ ζ) := by
  have hle1 : ∀ t, euclideanHausdorffOne d (dichFamily F E₀ ζ t) ≤ 1 := fun t => by
    have h := ((ccurveSpace_measure_comparison he hα hα2
      (ccurveSpaceK_subset e α k (ζ t).2)).1 univ).2
    rw [image_univ] at h
    simpa using (measure_mono (fun x hx => hx.2 : dichFamily F E₀ ζ t ⊆ _)).trans h
  refine ⟨fun t => ⟨measurableSet_dichFamily hF hE₀ ζ t, ?_⟩, fun A hA => ?_, ?_, fun A hA hA0 => ?_⟩
  · refine ⟨(hle1 t).trans_lt ENNReal.one_lt_top, fun _ => ccurveExt (ζ t : C(I, Vec d)),
      fun _ => ⟨1, lipschitzWith_ccurveExt (ccurveSpaceK_subset e α k (ζ t).2)⟩, ?_⟩
    have : dichFamily F E₀ ζ t \ ⋃ _ : ℕ, range (ccurveExt (ζ t : C(I, Vec d))) = ∅ := by
      refine eq_empty_of_forall_notMem fun x ⟨hx, hx'⟩ => hx' ?_
      obtain ⟨s, hs⟩ := hx.2
      exact mem_iUnion.2 ⟨0, s, by rw [ccurveExt_coe]; exact hs⟩
    rw [this, measure_empty]
  · have hB : MeasurableSet (Subtype.val '' E₀ ∩ F ∩ A : Set (Vec d)) :=
      ((measurableSet_image_val hE₀).inter hF).inter hA
    have hfun : (fun t => euclideanHausdorffOne d (dichFamily F E₀ ζ t ∩ A)) =
        (fun γ : ccurveSpace e α => euclideanHausdorffOne d
          ((Subtype.val '' E₀ ∩ F ∩ A) ∩ range (γ : C(I, Vec d)))) ∘
          (Set.inclusion (ccurveSpaceK_subset e α k)) ∘ ζ := by
      funext t
      simp only [Function.comp_apply, dichFamily, Set.inclusion]
      congr 1
      ext x
      simp only [mem_inter_iff]
      tauto
    rw [hfun]
    exact ((measurable_hausdorffOne_inter_range he hα hα2 hB).comp
      (continuous_inclusion (ccurveSpaceK_subset e α k)).measurable).comp hζ
  · calc ∫⁻ t, euclideanHausdorffOne d (dichFamily F E₀ ζ t) ≤ ∫⁻ _ : I, 1 :=
          lintegral_mono hle1
      _ < ⊤ := by simp
  · -- absolute continuity
    set W : Set (curveBall d k) := Subtype.val ⁻¹' (F ∩ A) with hW
    have hWm : MeasurableSet W := measurable_subtype_coe (hF.inter hA)
    have hW0 : dichMeasure μ F k W = 0 := by
      exact dichMeasure_preimage_null μ hF k (measure_mono_null inter_subset_right hA0)
    have hmix : mixMeasure (curveLawK e α k) (τ : Measure _) (E₀ ∩ W) = 0 := by
      have := hac hW0
      rwa [Measure.restrict_apply hWm, inter_comm] at this
    have hpt : ∀ t, euclideanHausdorffOne d (dichFamily F E₀ ζ t ∩ A) ≤
        (curveLawK e α k (ζ t) : Measure (curveBall d k)) (E₀ ∩ W) := fun t => by
      have hB : MeasurableSet (Subtype.val '' E₀ ∩ F ∩ A : Set (Vec d)) :=
        ((measurableSet_image_val hE₀).inter hF).inter hA
      have h1 := (hausdorff_le_law_and_law_le he hα hα2 (ζ t) hB).1
      have hset : dichFamily F E₀ ζ t ∩ A =
          (Subtype.val '' E₀ ∩ F ∩ A) ∩ range ((ζ t : ccurveSpaceK e α k) : C(I, Vec d)) := by
        ext x
        simp only [dichFamily, mem_inter_iff]
        tauto
      have hpre : Subtype.val ⁻¹' (Subtype.val '' E₀ ∩ F ∩ A : Set (Vec d)) = E₀ ∩ W := by
        ext y
        simp [hW, and_assoc]
      rw [hset]
      rwa [hpre] at h1
    refine le_antisymm ?_ bot_le
    calc ∫⁻ t, euclideanHausdorffOne d (dichFamily F E₀ ζ t ∩ A)
        ≤ ∫⁻ t, (curveLawK e α k (ζ t) : Measure (curveBall d k)) (E₀ ∩ W) := lintegral_mono hpt
      _ = 0 := by
        rw [lintegral_curveLawK_zeta τ hζ hζτ (hE₀.inter hWm), hmix]

end AFree
