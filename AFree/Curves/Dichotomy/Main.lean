module

public import AFree.Curves.Dichotomy.FamilyPos

/-!
# The dichotomy [AM, Lemma 7.3]

Either `μ⌞F` is concentrated on a Borel `C`-null set, or there is a rectifiable family of sets
covered by countably many `C¹` arcs whose tangents lie in `C ∪ (-C)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- [AM, Lemma 7.3]: for a finite measure `μ`, a Borel set
`F` with `μ F > 0` and the cone `C = C(e, α)`, either `μ⌞F` is concentrated on a Borel `C`-null set,
or there is a family `E : [0,1] → Set (ℝ^d)` with `IsRectifiableFamily (μ.restrict F) E`,
`E_t ⊆ F`, `∫ 𝓗¹(E_t ∩ F) dt > 0`, such that for a.e. `t` there are countably many `C¹` arcs
`(γ_n, J_n)` for which `𝓗¹`-a.e. `x ∈ E_t ∩ F` equals `γ_n(s)` for some `n` and `s ∈ J_n` with
`γ_n'(s) ∈ C ∪ -C`. -/
theorem dichotomy {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) (μ : Measure (Vec d)) [IsFiniteMeasure μ] {F : Set (Vec d)}
    (hF : MeasurableSet F) (hμF : 0 < μ F) :
    (∃ N : Set (Vec d), MeasurableSet N ∧ IsCNull (cone e α) N ∧ μ (F \ N) = 0) ∨
    ∃ E : I → Set (Vec d), (∀ t, E t ⊆ F) ∧ IsRectifiableFamily (μ.restrict F) E ∧
      0 < ∫⁻ t, euclideanHausdorffOne d (E t ∩ F) ∧
      ∀ᵐ t, ∃ (γ : ℕ → ℝ → Vec d) (J : ℕ → Set ℝ), (∀ n, IsC1Arc (γ n) (J n)) ∧
        ∀ᵐ x ∂(euclideanHausdorffOne d).restrict (E t ∩ F), ∃ n, ∃ s ∈ J n, γ n s = x ∧
          deriv (γ n) s ∈ cone e α ∪ -cone e α := by
  have _ := hμF
  by_cases h : ∀ k : ℕ, ∃ E : Set (curveBall d k), MeasurableSet E ∧
      dichMeasure μ F k Eᶜ = 0 ∧
      ∀ y : ccurveSpaceK e α k, (curveLawK e α k y : Measure (curveBall d k)) E = 0
  · exact Or.inl (dichotomy_case_concentrated he hα hα2 μ hF h)
  · right
    obtain ⟨k, hk⟩ := not_forall.1 h
    obtain ⟨τ, E₀, hE₀, hne, hac⟩ := (rainwater_prop (continuous_curveLawK e α k)
      (dichMeasure μ F k)).resolve_left fun ⟨E, hE, h1, h2⟩ => hk ⟨E, hE, h1, h2⟩
    obtain ⟨ζ, hζ, hζτ⟩ := exists_measurable_map_unitInterval_eq (τ : Measure (ccurveSpaceK e α k))
    refine ⟨dichFamily F E₀ ζ, dichFamily_subset F E₀ ζ,
      dichotomy_family_construction he hα hα2 μ hF τ hE₀ hac hζ hζτ,
      dichotomy_family_positivity he hα hα2 μ hF τ hE₀ hac hne hζ hζτ,
      Filter.Eventually.of_forall fun t => ?_⟩
    obtain ⟨g, J, S, hJ, hSJ, hgS, hnull⟩ := dichotomy_family_arcs hα hα2 F E₀ ζ t
    refine ⟨g, J, hJ, ?_⟩
    have hm : MeasurableSet (dichFamily F E₀ ζ t ∩ F) :=
      (measurableSet_dichFamily hF hE₀ ζ t).inter hF
    rw [ae_restrict_iff' hm]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxE
    have hxE' : x ∈ dichFamily F E₀ ζ t := hxE.1
    by_contra hcon
    refine hx ⟨hxE', fun hx' => hcon ?_⟩
    obtain ⟨n, s, hs, rfl⟩ := mem_iUnion.1 hx'
    exact ⟨n, s, hSJ n hs, rfl, Or.inl (hgS n s hs).2⟩

end AFree
