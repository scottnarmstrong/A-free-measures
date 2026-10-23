module

public import AFree.Curves.Dichotomy.Setup

/-!
# The dichotomy, case A: concentration on a Borel `C`-null set

First case of the proof of [AM, Lemma 7.3].
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- `λ_γ(val '' E) = λ_γ^{(k)}(E)` for `γ ∈ 𝒢_k` and `E ⊆ B(k+1)` Borel. -/
lemma curveLaw_image_val {e : Vec d} {α : ℝ} {k : ℕ} (γ : ccurveSpaceK e α k)
    {E : Set (curveBall d k)} (hE : MeasurableSet E) :
    curveLaw (γ : C(I, Vec d)) (Subtype.val '' E) =
      (curveLawK e α k γ : Measure (curveBall d k)) E := by
  have hm : MeasurableSet (Subtype.val '' E) :=
    (MeasurableEmbedding.subtype_coe (measurableSet_curveBall k)).measurableSet_image.2 hE
  rw [← map_val_curveLawK, Measure.map_apply measurable_subtype_coe hm,
    Subtype.val_injective.preimage_image]

/-- If the first alternative of the variant [AM, Corollary 7.2] of Rainwater's lemma holds for every
`k` (for `μ_k`, `Y = 𝒢_k`, `Φ(γ) = λ_γ`), then `μ⌞F` is concentrated on a Borel `C`-null set. -/
theorem dichotomy_case_concentrated {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ}
    (hα : 0 < α) (hα2 : α < Real.pi / 2) (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {F : Set (Vec d)} (hF : MeasurableSet F)
    (h : ∀ k : ℕ, ∃ E : Set (curveBall d k), MeasurableSet E ∧ dichMeasure μ F k Eᶜ = 0 ∧
      ∀ y : ccurveSpaceK e α k, (curveLawK e α k y : Measure (curveBall d k)) E = 0) :
    ∃ N : Set (Vec d), MeasurableSet N ∧ IsCNull (cone e α) N ∧ μ (F \ N) = 0 := by
  choose E hE hEμ hEl using h
  have himg : ∀ k, MeasurableSet (Subtype.val '' E k : Set (Vec d)) := fun k =>
    (MeasurableEmbedding.subtype_coe (measurableSet_curveBall k)).measurableSet_image.2 (hE k)
  refine ⟨⋃ k, Subtype.val '' E k ∩ dichAnnulus d k,
    MeasurableSet.iUnion fun k => (himg k).inter (measurableSet_dichAnnulus k), ?_, ?_⟩
  · intro G hG
    rw [iUnion_inter]
    refine measure_iUnion_null fun k => measure_mono_null ?_
      ((ccurve_cut he hα hα2 hG k).2 (Subtype.val '' E k) fun ζ hζ => ?_)
    · rintro x ⟨⟨hxE, hxA⟩, hxG⟩
      exact ⟨⟨hxE, dichAnnulus_subset_ball k hxA⟩, hxG⟩
    · have := curveLaw_image_val (e := e) (α := α) (k := k) ⟨ζ, hζ⟩ (hE k)
      rw [curveLaw_apply _ (himg k), hEl k ⟨ζ, hζ⟩] at this
      exact this
  · refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null fun k =>
      show μ ((F ∩ dichAnnulus d k) \ Subtype.val '' E k) = 0 from ?_)
    · obtain ⟨hxF, hxN⟩ := hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 (iUnion_dichAnnulus.symm ▸ mem_univ x)
      exact mem_iUnion.2 ⟨k, ⟨hxF, hk⟩, fun hxE => hxN (mem_iUnion.2 ⟨k, hxE, hk⟩)⟩
    · refine measure_mono_null (t := Subtype.val '' (E k)ᶜ ∩ (F ∩ dichAnnulus d k)) ?_ ?_
      · rintro x ⟨⟨hxF, hxA⟩, hxE⟩
        obtain ⟨y, rfl⟩ : x ∈ range (Subtype.val : curveBall d k → Vec d) :=
          by rw [Subtype.range_coe]; exact dichAnnulus_subset_curveBall k hxA
        exact ⟨⟨y, fun hy => hxE ⟨y, hy, rfl⟩, rfl⟩, hxF, hxA⟩
      · rw [← dichMeasure_apply μ hF k]
        exact hEμ k

end AFree
