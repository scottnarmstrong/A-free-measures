module

public import AFree.Curves.Dichotomy.Family
public import AFree.Curves.Dichotomy.Arcs

/-!
# The dichotomy, case B: positivity and the `C¹` arcs of the family

Second case of the proof of [AM, Lemma 7.3]: the family has positive mass and is covered by `C¹` arcs.
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- Under the hypotheses of `dichotomy_family_construction`
and `[τ]_Φ⌞E₀ ≠ 0`, `∫ 𝓗¹(E_t ∩ F) dt > 0`. -/
theorem dichotomy_family_positivity {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ}
    (hα : 0 < α) (hα2 : α < Real.pi / 2) (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {F : Set (Vec d)} (hF : MeasurableSet F) {k : ℕ} (τ : ProbabilityMeasure (ccurveSpaceK e α k))
    {E₀ : Set (curveBall d k)} (hE₀ : MeasurableSet E₀)
    (hac : (mixMeasure (curveLawK e α k) (τ : Measure _)).restrict E₀ ≪ dichMeasure μ F k)
    (hne : (mixMeasure (curveLawK e α k) (τ : Measure _)).restrict E₀ ≠ 0)
    {ζ : I → ccurveSpaceK e α k} (hζ : Measurable ζ) (hζτ : Measure.map ζ volume = (τ : Measure _)) :
    0 < ∫⁻ t, euclideanHausdorffOne d (dichFamily F E₀ ζ t ∩ F) := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  set WF : Set (curveBall d k) := Subtype.val ⁻¹' F with hWFdef
  have hWF : MeasurableSet WF := measurable_subtype_coe hF
  set mix := mixMeasure (curveLawK e α k) (τ : Measure _) with hmix
  have hcompl : mix.restrict E₀ WFᶜ = 0 := by
    refine hac ?_
    have := dichMeasure_preimage_null μ hF k (W := Fᶜ) (by
      rw [Measure.restrict_apply' hF]; simp)
    rwa [preimage_compl] at this
  have hpos : mix (WF ∩ E₀) ≠ 0 := by
    intro h0
    refine hne (Measure.measure_univ_eq_zero.1 ?_)
    have h1 : mix.restrict E₀ WF = 0 := by rwa [Measure.restrict_apply hWF]
    have : (univ : Set (curveBall d k)) = WF ∪ WFᶜ := (union_compl_self _).symm
    rw [this]
    exact measure_union_null h1 hcompl
  have hB : MeasurableSet (Subtype.val '' E₀ ∩ F : Set (Vec d)) :=
    (measurableSet_image_val hE₀).inter hF
  have hpt : ∀ t, ENNReal.ofReal (Real.cos α) *
      (curveLawK e α k (ζ t) : Measure (curveBall d k)) (WF ∩ E₀) ≤
        euclideanHausdorffOne d (dichFamily F E₀ ζ t ∩ F) := fun t => by
    have h2 := (hausdorff_le_law_and_law_le he hα hα2 (ζ t) hB).2
    have hset : dichFamily F E₀ ζ t ∩ F = (Subtype.val '' E₀ ∩ F) ∩
        range ((ζ t : ccurveSpaceK e α k) : C(I, Vec d)) := by
      ext x
      simp only [dichFamily, mem_inter_iff]
      tauto
    have hpre : Subtype.val ⁻¹' (Subtype.val '' E₀ ∩ F : Set (Vec d)) = WF ∩ E₀ := by
      ext y
      simp [hWFdef, and_comm]
    rw [hset]
    rw [hpre] at h2
    calc ENNReal.ofReal (Real.cos α) * (curveLawK e α k (ζ t) : Measure (curveBall d k)) (WF ∩ E₀)
        ≤ ENNReal.ofReal (Real.cos α) * (ENNReal.ofReal (Real.cos α)⁻¹ *
          euclideanHausdorffOne d ((Subtype.val '' E₀ ∩ F) ∩
            range ((ζ t : ccurveSpaceK e α k) : C(I, Vec d)))) := by gcongr
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne']
        simp
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (Real.cos α) * mix (WF ∩ E₀) :=
        ENNReal.mul_pos (by simpa using hc) hpos
    _ = ∫⁻ t, ENNReal.ofReal (Real.cos α) *
          (curveLawK e α k (ζ t) : Measure (curveBall d k)) (WF ∩ E₀) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_curveLawK_zeta τ hζ hζτ (hWF.inter hE₀)]
    _ ≤ _ := lintegral_mono hpt

/-- For every `t`, the set `E_t` is covered up to an `𝓗¹`-null set by
countably many `C¹` arcs `(γ_n, J_n)` and sets `S_n ⊆ J_n` with `γ_n(s) ∈ E_t` and
`γ_n'(s) ∈ C` for `s ∈ S_n`. -/
theorem dichotomy_family_arcs {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2) {k : ℕ}
    (F : Set (Vec d)) (E₀ : Set (curveBall d k)) (ζ : I → ccurveSpaceK e α k) (t : I) :
    ∃ (g : ℕ → ℝ → Vec d) (J S : ℕ → Set ℝ), (∀ n, IsC1Arc (g n) (J n)) ∧ (∀ n, S n ⊆ J n) ∧
      (∀ n, ∀ s ∈ S n, g n s ∈ dichFamily F E₀ ζ t ∧ deriv (g n) s ∈ cone e α) ∧
      euclideanHausdorffOne d (dichFamily F E₀ ζ t \ ⋃ n, g n '' S n) = 0 := by
  obtain ⟨g, J, S, hJ, hS, hgS, hnull⟩ :=
    ccurve_arcs hα hα2 (ccurveSpaceK_subset e α k (ζ t).2)
  refine ⟨g, J, fun n => {s | s ∈ S n ∧ g n s ∈ dichFamily F E₀ ζ t}, hJ,
    fun n s hs => (hS n hs.1).1, fun n s hs => ⟨hs.2, (hgS n s hs.1).2⟩, ?_⟩
  refine measure_mono_null ?_ hnull
  intro x hx
  refine ⟨hx.1.2, fun hx' => hx.2 ?_⟩
  obtain ⟨n, s, hs, rfl⟩ := mem_iUnion.1 hx'
  exact mem_iUnion.2 ⟨n, s, ⟨hs, hx.1⟩, rfl⟩

end AFree
