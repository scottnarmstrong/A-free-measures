module

public import AFree.Curves.Rainwater.Mix
public import AFree.Curves.Rainwater.Lemma
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The convex-hull form of [AM, Corollary 7.2]
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace AFree

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- `{[τ]_Φ : τ ∈ 𝒫(Y)}` is compact and convex in
`𝒫(X)`. -/
theorem rainwater_prop_convex_compact_hull {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ) :
    IsCompact (range (mixPM hΦ)) ∧
      Convex ℝ≥0 ((fun l : ProbabilityMeasure X => (l : Measure X)) '' range (mixPM hΦ)) := by
  refine ⟨isCompact_range (continuous_mixPM hΦ), ?_⟩
  rintro _ ⟨_, ⟨τ₁, rfl⟩, rfl⟩ _ ⟨_, ⟨τ₂, rfl⟩, rfl⟩ a b _ _ hab
  have hprob : IsProbabilityMeasure (a • (τ₁ : Measure Y) + b • (τ₂ : Measure Y)) := by
    refine ⟨?_⟩
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
    rw [← ENNReal.coe_add, hab, ENNReal.coe_one]
  refine ⟨mixPM hΦ ⟨_, hprob⟩, ⟨_, rfl⟩, ?_⟩
  change mixMeasure Φ (a • (τ₁ : Measure Y) + b • (τ₂ : Measure Y)) = _
  exact mixMeasure_add_smul hΦ _ _ a b

omit [CompactSpace X] [CompactSpace Y] in
/-- `[δ_y]_Φ = Φ(y)`. -/
lemma mixMeasure_dirac {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ) (y : Y) :
    mixMeasure Φ (Measure.dirac y) = (Φ y : Measure X) :=
  Measure.dirac_bind (measurable_coe_of_continuous hΦ) y

/-- If `μ ⟂ [τ]_Φ` for all `τ`, then (i) holds. -/
theorem rainwater_prop_case_singular {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ)
    (μ : Measure X) [IsFiniteMeasure μ]
    (hsing : ∀ τ : ProbabilityMeasure Y, μ ⟂ₘ mixMeasure Φ τ) :
    ∃ E : Set X, MeasurableSet E ∧ μ Eᶜ = 0 ∧ ∀ y, (Φ y : Measure X) E = 0 := by
  obtain ⟨hcomp, hconv⟩ := rainwater_prop_convex_compact_hull hΦ
  obtain ⟨E, hE, hμE, hl⟩ := rainwater_lemma _ hcomp hconv μ (by
    rintro _ ⟨τ, rfl⟩
    exact hsing τ)
  refine ⟨E, hE, hμE, fun y => ?_⟩
  have := hl (mixPM hΦ ⟨Measure.dirac y, inferInstance⟩) ⟨_, rfl⟩
  have e : ((mixPM hΦ ⟨Measure.dirac y, inferInstance⟩ : ProbabilityMeasure X) : Measure X) =
      Φ y := mixMeasure_dirac hΦ y
  rwa [e] at this

omit [CompactSpace Y] in
/-- If `¬ μ ⟂ [τ]_Φ` for some `τ`, then (ii) holds. -/
theorem rainwater_prop_case_nonsingular {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ)
    (μ : Measure X) [IsFiniteMeasure μ] (τ : ProbabilityMeasure Y)
    (h : ¬ μ ⟂ₘ mixMeasure Φ τ) :
    ∃ E : Set X, MeasurableSet E ∧ (mixMeasure Φ τ).restrict E ≠ 0 ∧
      (mixMeasure Φ τ).restrict E ≪ μ := by
  have := isProbabilityMeasure_mixMeasure hΦ τ
  set ν := mixMeasure Φ τ with hν
  obtain ⟨N, hN, hμN, hsN⟩ := (Measure.mutuallySingular_singularPart ν μ).symm
  refine ⟨Nᶜ, hN.compl, fun h0 => h ⟨N, hN, hμN, ?_⟩, ?_⟩
  · have := Measure.restrict_apply_univ (μ := ν) (s := Nᶜ)
    rw [h0] at this
    simpa using this.symm
  · have hdec := Measure.haveLebesgueDecomposition_add ν μ
    have h1 : (ν.singularPart μ).restrict Nᶜ = 0 := Measure.restrict_eq_zero.2 hsN
    have h2 := congrArg (fun m : Measure X => m.restrict Nᶜ) hdec
    simp only [Measure.restrict_add, h1, zero_add] at h2
    rw [h2]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (withDensity_absolutelyContinuous μ _)

/-- Let `X`, `Y` be compact metric spaces, `Φ : Y → 𝒫(X)` continuous and `μ` a
finite Borel measure on `X`. Either (i) there is a Borel `E` with
`μ(Eᶜ) = 0` and `Φ(y)(E) = 0` for all `y`; or (ii) there are a Borel probability measure `τ` on
`Y` and a Borel `E` with `[τ]_Φ⌞E ≠ 0` and `[τ]_Φ⌞E ≪ μ`, `[τ]_Φ = ∫ Φ(y) dτ(y)`
(`mixMeasure Φ τ`). -/
theorem rainwater_prop {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ) (μ : Measure X)
    [IsFiniteMeasure μ] :
    (∃ E : Set X, MeasurableSet E ∧ μ Eᶜ = 0 ∧ ∀ y, (Φ y : Measure X) E = 0) ∨
    ∃ (τ : ProbabilityMeasure Y) (E : Set X), MeasurableSet E ∧
      (mixMeasure Φ τ).restrict E ≠ 0 ∧ (mixMeasure Φ τ).restrict E ≪ μ := by
  by_cases h : ∀ τ : ProbabilityMeasure Y, μ ⟂ₘ mixMeasure Φ τ
  · exact Or.inl (rainwater_prop_case_singular hΦ μ h)
  · obtain ⟨τ, hτ⟩ := not_forall.1 h
    obtain ⟨E, hE, h1, h2⟩ := rainwater_prop_case_nonsingular hΦ μ τ hτ
    exact Or.inr ⟨τ, E, hE, h1, h2⟩

end AFree
