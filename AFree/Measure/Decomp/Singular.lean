module

public import AFree.Measure.PolarFacts

/-!
# Singular parts: localization, absolute continuity, dimension zero, transfer

Lebesgue singular parts of measures, including the case of `Vec 0` without finiteness.
-/

public section

open MeasureTheory

namespace AFree

open PDE

section Comparison

variable {d : ℕ}

/-- Common core of the next two lemmas: if `ν` is finite, `G` is Borel with `νˢ(G) = 0` and
`μ` vanishes on every Borel `E ⊆ G` on which `ν` vanishes, then `μˢ(G) = 0`. -/
theorem singularPart_apply_eq_zero_of_null (μ ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {G : Set (Vec d)} (hG : MeasurableSet G) (hν : ν.singularPart volume G = 0)
    (hμ : ∀ E, MeasurableSet E → E ⊆ G → ν E = 0 → μ E = 0) :
    μ.singularPart volume G = 0 := by
  obtain ⟨S, hS, h1, h2⟩ := Measure.mutuallySingular_singularPart μ (volume : Measure (Vec d))
  have hdec := Measure.singularPart_add_rnDeriv ν (volume : Measure (Vec d))
  have hE : ν (G ∩ Sᶜ) = 0 := by
    rw [← hdec, Measure.add_apply]
    have a1 : ν.singularPart volume (G ∩ Sᶜ) = 0 :=
      measure_mono_null Set.inter_subset_left hν
    have a2 : (volume.withDensity (ν.rnDeriv volume)) (G ∩ Sᶜ) = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_mono_null Set.inter_subset_right h2)
    rw [a1, a2, add_zero]
  have h3 : μ (G ∩ Sᶜ) = 0 := hμ _ (hG.inter hS.compl) Set.inter_subset_left hE
  refine le_antisymm ?_ bot_le
  calc μ.singularPart volume G ≤ μ.singularPart volume (G ∩ Sᶜ) + μ.singularPart volume S := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro x hx
        by_cases hxS : x ∈ S
        · exact Or.inr hxS
        · exact Or.inl ⟨hx, hxS⟩
    _ ≤ μ (G ∩ Sᶜ) + 0 := add_le_add (Measure.singularPart_le μ volume _) h1.le
    _ = 0 := by rw [h3, add_zero]

/-- If `ν` is finite and `μ ≪ ν`, then `μˢ ≪ νˢ`. No finiteness of `μ` is needed. -/
theorem singularPart_absolutelyContinuous_of_ac (μ ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (h : μ ≪ ν) : μ.singularPart volume ≪ ν.singularPart volume := by
  intro B hB
  have hB' : ν.singularPart volume (toMeasurable (ν.singularPart volume) B) = 0 := by
    rw [measure_toMeasurable]; exact hB
  refine measure_mono_null (subset_toMeasurable _ B)
    (singularPart_apply_eq_zero_of_null μ ν (measurableSet_toMeasurable _ _) hB' ?_)
  intro E _ _ hE
  exact h hE

/-- If `A` is Borel with `τ A < ∞` and `F ⊆ A` with `(τ ⌞ A)ˢ(F) = 0`, then
`τˢ(F) = 0`. -/
theorem singularPart_apply_eq_zero_of_restrict (τ : Measure (Vec d)) {A : Set (Vec d)}
    (hA : MeasurableSet A) (hτ : τ A < ⊤) {F : Set (Vec d)} (hFA : F ⊆ A)
    (hF : (τ.restrict A).singularPart volume F = 0) : τ.singularPart volume F = 0 := by
  have : IsFiniteMeasure (τ.restrict A) := ⟨by simpa [Measure.restrict_apply_univ] using hτ⟩
  set H := toMeasurable ((τ.restrict A).singularPart volume) F ∩ A with hH
  have hHm : MeasurableSet H := (measurableSet_toMeasurable _ _).inter hA
  have hH0 : (τ.restrict A).singularPart volume H = 0 :=
    measure_mono_null Set.inter_subset_left (by rw [measure_toMeasurable]; exact hF)
  have hFH : F ⊆ H := fun x hx => ⟨subset_toMeasurable _ F hx, hFA hx⟩
  refine measure_mono_null hFH
    (singularPart_apply_eq_zero_of_null τ (τ.restrict A) hHm hH0 ?_)
  intro E hE hEH hE0
  rw [Measure.restrict_apply hE, Set.inter_eq_left.2 (hEH.trans Set.inter_subset_right)] at hE0
  exact hE0

end Comparison

/-- On `Vec 0` every measure has zero Lebesgue singular part (no finiteness). -/
theorem singularPart_eq_zero_of_dimZero (μ : Measure (Vec 0)) :
    μ.singularPart volume = 0 := by
  apply Measure.singularPart_eq_zero_of_ac
  intro s hs
  have hvol : (volume : Measure (Vec 0)) = Measure.dirac default := by
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) = _
    rw [Measure.pi_of_empty]
    congr 1; exact Subsingleton.elim _ _
  by_cases hne : s.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hx' : x = default := Subsingleton.elim _ _
    subst hx'
    rw [hvol, Measure.dirac_apply_of_mem hx] at hs
    exact absurd hs one_ne_zero
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp

/-- Application form: on `Vec 0` every property holds `μˢ`-a.e. -/
theorem ae_singularPart_of_dimZero (μ : Measure (Vec 0)) (p : Vec 0 → Prop) :
    ∀ᵐ x ∂(μ.singularPart volume), p x := by
  rw [singularPart_eq_zero_of_dimZero μ]
  simp

/-- If the polar of `μ` lies in `W` `|μ|ˢ`-a.e., then for `|μˢ|`-a.e. `x` the polar
of `μˢ` lies in `W` and has Euclidean norm one (in particular it is nonzero). -/
theorem ae_polar_lebesgueSingularPart_mem {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (W : Set (ι → ℝ))
    (h : ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ W) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart μ),
      polar (lebesgueSingularPart μ) x ∈ W ∧ piEuclideanNorm (polar (lebesgueSingularPart μ) x) = 1 ∧
        polar (lebesgueSingularPart μ) x ≠ 0 := by
  rw [← euclideanVariation_lebesgueSingularPart] at h
  filter_upwards [h, polar_lebesgueSingularPart_ae μ,
    piEuclideanNorm_polar_eq_one (lebesgueSingularPart μ)] with x h1 h2 h3
  refine ⟨h2 ▸ h1, h3, fun h0 => ?_⟩
  rw [h0] at h3
  simp [piEuclideanNorm] at h3

end AFree
