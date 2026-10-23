module

public import AFree.Curves.GraphFormRep

/-!
# `C`-null sets via the graph parameter

A set is `C(e, α)`-null iff its preimage under every graph parametrization is `𝓛¹`-null.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

private lemma graph_comparison {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {u₀ u₁ : ℝ} (hu : u₀ ≤ u₁) {η : ℝ → Vec d}
    (hη : IsConeGraphFn e α u₀ u₁ η) (E : Set (Vec d)) :
    volume (Icc u₀ u₁ ∩ graphCurve e η ⁻¹' E) ≤
        euclideanHausdorffOne d (E ∩ graphCurve e η '' Icc u₀ u₁) ∧
      euclideanHausdorffOne d (E ∩ graphCurve e η '' Icc u₀ u₁) ≤
        ENNReal.ofReal (1 / Real.cos α) * volume (Icc u₀ u₁ ∩ graphCurve e η ⁻¹' E) := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  obtain ⟨hnorm, -, hinj, hdot, -⟩ := graphCurve_isCCurve he hα hα2 hu hη
  set P : Set ℝ := Icc u₀ u₁ ∩ graphCurve e η ⁻¹' E with hP
  have hS : E ∩ graphCurve e η '' Icc u₀ u₁ = graphCurve e η '' P := by
    ext x
    constructor
    · rintro ⟨hxE, u, hu', rfl⟩; exact ⟨u, ⟨hu', hxE⟩, rfl⟩
    · rintro ⟨u, ⟨hu', hxE⟩, rfl⟩; exact ⟨hxE, u, hu', rfl⟩
  constructor
  · have hπ : ∀ x y : Vec d, |vecDot x e - vecDot y e| ≤ vecEuclideanNorm (x - y) := by
      intro x y
      rw [← vecDot_sub_left]
      simpa [he] using abs_vecDot_le_vecEuclideanNorm_mul (x - y) e
    have := volume_image_le_hausdorffOne (π := fun x : Vec d => vecDot x e) hπ
      (E ∩ graphCurve e η '' Icc u₀ u₁)
    refine le_trans (le_of_eq ?_) this
    rw [hS, image_image]
    rw [image_congr (g := id) (fun u hu' => hdot u hu'.1), image_id]
  · rw [hS]
    have := hausdorffOne_image_le_pos (B := Icc u₀ u₁) (A := P) (γ := graphCurve e η)
      (inter_subset_left) (L := Real.toNNReal (1 / Real.cos α)) (by simpa using hc)
      (fun x hx y hy => by
        rw [Real.coe_toNNReal _ (by positivity)]
        refine (hnorm y hy x hx).trans (le_of_eq ?_)
        ring)
    exact this

/-- For every `E ⊆ ℝ^d` and
`η` as above, `𝓛¹(γ_η⁻¹(E)) ≤ 𝓗¹(E ∩ G) ≤ (1/cos α) 𝓛¹(γ_η⁻¹(E))` with `G = γ_η([u₀, u₁])`
and `γ_η⁻¹(E)` taken inside `[u₀, u₁]`; hence `E` is `C(e, α)`-null iff
`𝓛¹(γ_η⁻¹(E)) = 0` for every such `η`. -/
theorem graphform_comparison_and_null_iff {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ}
    (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    (∀ (E : Set (Vec d)) (u₀ u₁ : ℝ) (η : ℝ → Vec d), u₀ ≤ u₁ → IsConeGraphFn e α u₀ u₁ η →
      volume (Icc u₀ u₁ ∩ graphCurve e η ⁻¹' E) ≤
          euclideanHausdorffOne d (E ∩ graphCurve e η '' Icc u₀ u₁) ∧
        euclideanHausdorffOne d (E ∩ graphCurve e η '' Icc u₀ u₁) ≤
          ENNReal.ofReal (1 / Real.cos α) * volume (Icc u₀ u₁ ∩ graphCurve e η ⁻¹' E)) ∧
    ∀ E : Set (Vec d), IsCNull (cone e α) E ↔
      ∀ (u₀ u₁ : ℝ) (η : ℝ → Vec d), u₀ ≤ u₁ → IsConeGraphFn e α u₀ u₁ η →
        volume (Icc u₀ u₁ ∩ graphCurve e η ⁻¹' E) = 0 := by
  refine ⟨fun E u₀ u₁ η hu hη => graph_comparison he hα hα2 hu hη E, fun E => ⟨?_, ?_⟩⟩
  · intro hE u₀ u₁ η hu hη
    have h1 := (graph_comparison he hα hα2 hu hη E).1
    have h2 := hE _ (graphCurve_isCCurve he hα hα2 hu hη).2.2.2.2
    rw [h2] at h1
    exact le_antisymm h1 bot_le
  · intro h G hG
    obtain ⟨u₀, u₁, η, hu, hη, rfl⟩ := ccurve_exists_graph he hα hα2 hG
    have := (graph_comparison he hα hα2 hu hη E).2
    rw [h u₀ u₁ η hu hη, mul_zero] at this
    exact le_antisymm this bot_le

end AFree
