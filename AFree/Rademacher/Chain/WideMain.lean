module

public import AFree.Rademacher.Chain.Wide

/-!
# AM Proposition 4.10: wide cones, the main statement

Main statement of [AM, Proposition 4.10] for finite measures `μ`.
-/

@[expose] public section

open PDE MeasureTheory Set
open scoped ENNReal NNReal unitInterval

namespace AFree.Rademacher

variable {d : ℕ}

/-- Case (ii) is impossible: for `V ∈ 𝒢_μ`, a set `C` with
`V(x) ∩ C = {0}` for `μ`-a.e. `x ∈ F`, and a family `E` as in (ii)\*, one has
`∫ 𝓗¹(E_t ∩ F) dt = 0`. -/
theorem wideconenull_contradiction {μ : Measure (Vec d)} {V : Vec d → Submodule ℝ (Vec d)}
    (hV : IsDecompTestField μ V) {F : Set (Vec d)} {C : Set (Vec d)}
    (hCV : ∀ᵐ x ∂μ, x ∈ F → ∀ w ∈ V x, w ∈ C → w = 0) {E : I → Set (Vec d)}
    (hrect : IsRectifiableFamily (μ.restrict F) E)
    (harcs : ∀ᵐ t : I, ∃ (γ : ℕ → ℝ → Vec d) (J : ℕ → Set ℝ), (∀ n, IsC1Arc (γ n) (J n)) ∧
      ∀ᵐ x ∂(euclideanHausdorffOne d).restrict (E t ∩ F),
        ∃ n, ∃ s ∈ J n, γ n s = x ∧ deriv (γ n) s ∈ C ∪ -C) :
    ∫⁻ t, euclideanHausdorffOne d (E t ∩ F) = 0 := by
  have hrectμ := wideconenull_family_rectifiable hrect
  obtain ⟨Z, hZ0, hZm, hμZ⟩ := exists_measurable_superset_of_null (ae_iff.1 hCV)
  have hex := wideconenull_exceptional_null_set hrectμ hZm hμZ
  have htest := hV.2 E hrectμ
  have hzero : ∀ᵐ t : I, euclideanHausdorffOne d (E t ∩ F) = 0 := by
    filter_upwards [hex, htest, harcs] with t h1 h2 ⟨γ, J, hγ, hae⟩
    set N0 : Set (Vec d) := {x | ¬ ∃ n, ∃ s ∈ J n, γ n s = x ∧ deriv (γ n) s ∈ C ∪ -C} with hN0
    have hN0null : euclideanHausdorffOne d (N0 ∩ (E t ∩ F)) = 0 :=
      le_antisymm ((Measure.le_restrict_apply _ _).trans_eq hae) bot_le
    have hB : ∀ n, euclideanHausdorffOne d
        {x ∈ E t ∩ γ n '' J n | ∃ s ∈ J n, γ n s = x ∧ deriv (γ n) s ∉ V x} = 0 :=
      fun n => wideconenull_arc_test (h2 (γ n) (J n) (hγ n))
    refine le_antisymm ?_ bot_le
    calc euclideanHausdorffOne d (E t ∩ F)
        ≤ euclideanHausdorffOne d ((E t ∩ Z) ∪ (N0 ∩ (E t ∩ F)) ∪
            ⋃ n, {x ∈ E t ∩ γ n '' J n | ∃ s ∈ J n, γ n s = x ∧ deriv (γ n) s ∉ V x}) := by
          refine measure_mono fun x hx => ?_
          by_cases hxZ : x ∈ Z
          · exact Or.inl (Or.inl ⟨hx.1, hxZ⟩)
          by_cases hxN : x ∈ N0
          · exact Or.inl (Or.inr ⟨hxN, hx⟩)
          right
          simp only [hN0, mem_ofPred_eq, not_not] at hxN
          obtain ⟨n, s, hs, hγs, hder⟩ := hxN
          refine mem_iUnion.2 ⟨n, ⟨hx.1, ⟨s, hs, hγs⟩⟩, ?_⟩
          by_contra hno
          have hVs : deriv (γ n) s ∈ V x := by
            by_contra hnV
            exact hno ⟨s, hs, hγs, hnV⟩
          have hxZ0 : x ∉ {x | ¬ (x ∈ F → ∀ w ∈ V x, w ∈ C → w = 0)} := fun h => hxZ (hZ0 h)
          simp only [mem_ofPred_eq, not_not] at hxZ0
          have hne : deriv (γ n) s ≠ 0 := (hγ n).2.2.2 s hs
          rcases hder with hC | hC
          · exact hne (hxZ0 hx.2 _ hVs hC)
          · have hmem : -deriv (γ n) s ∈ C := hC
            exact hne (neg_eq_zero.1 (hxZ0 hx.2 _ ((V x).neg_mem hVs) hmem))
      _ = 0 := by
          refine measure_union_null (measure_union_null h1 hN0null) (measure_iUnion_null hB)
  calc ∫⁻ t, euclideanHausdorffOne d (E t ∩ F) = ∫⁻ _t : I, (0 : ℝ≥0∞) :=
        lintegral_congr_ae hzero
    _ = 0 := lintegral_zero

/-- [AM, Proposition 4.10], for finite `μ`. Let `V ∈ 𝒢_μ`, `F` a Borel set and
`C = C(e, α)` a cone with `V(x) ∩ C = {0}` for `μ`-a.e. `x ∈ F`. Then there is a Borel `C`-null set
`F' ⊆ F` with `μ F' = μ F`. -/
theorem prop_wideconenull {μ : Measure (Vec d)} [IsFiniteMeasure μ] {V : Vec d → Submodule ℝ (Vec d)}
    (hV : IsDecompTestField μ V) {F : Set (Vec d)} (hF : MeasurableSet F) {e : Vec d}
    (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (hCV : ∀ᵐ x ∂μ, x ∈ F → ∀ w ∈ V x, w ∈ cone e α → w = 0) :
    ∃ F' : Set (Vec d), F' ⊆ F ∧ MeasurableSet F' ∧ IsCNull (cone e α) F' ∧ μ F' = μ F := by
  by_cases h0 : μ F = 0
  · refine ⟨∅, empty_subset _, MeasurableSet.empty, fun G _ => by simp, by simp [h0]⟩
  have hpos : 0 < μ F := pos_iff_ne_zero.2 h0
  rcases dichotomy he hα hα2 μ hF hpos with ⟨N, hN, hNnull, hμ⟩ | ⟨E, hEF, hrect, hint, harcs⟩
  · exact ⟨F ∩ N, wideconenull_case_concentrated hF hN hNnull hμ⟩
  · exact absurd (wideconenull_contradiction hV hCV hrect harcs) hint.ne'

end AFree.Rademacher
