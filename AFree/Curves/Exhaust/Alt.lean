module

public import AFree.Curves.Exhaust.Family
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Exhaustion, part 2: alternative (ii) of Rainwater's proposition cannot hold
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The piece `B ∩ B(k)` of the complement `B` of the maximal set. -/
def exhaustPiece (B : Set (Vec d)) (k : ℕ) : Set (Vec d) := B ∩ euclideanClosedBall 0 (k : ℝ)

lemma exhaustPiece_subset_curveBall (B : Set (Vec d)) (k : ℕ) :
    exhaustPiece B k ⊆ curveBall d k :=
  fun _ hx => euclideanClosedBall_mono (by positivity) (by linarith) hx.2

lemma measurableSet_curveBall (k : ℕ) : MeasurableSet (curveBall d k) :=
  (isClosed_euclideanClosedBall _ _).measurableSet

lemma measurableSet_exhaustPiece {B : Set (Vec d)} (hB : MeasurableSet B) (k : ℕ) :
    MeasurableSet (exhaustPiece B k) :=
  hB.inter (isClosed_euclideanClosedBall _ _).measurableSet

/-- `μ_k = μ⌞(B ∩ B(k))` as a measure on the compact ball `B(k+1)`. -/
noncomputable def pieceMeasure (μ : Measure (Vec d)) (B : Set (Vec d)) (k : ℕ) :
    Measure (curveBall d k) :=
  Measure.comap Subtype.val (μ.restrict (exhaustPiece B k))

lemma pieceMeasure_apply (μ : Measure (Vec d)) {B : Set (Vec d)} (hB : MeasurableSet B) (k : ℕ)
    (T : Set (curveBall d k)) :
    pieceMeasure μ B k T = μ (Subtype.val '' T ∩ exhaustPiece B k) := by
  rw [pieceMeasure, (MeasurableEmbedding.subtype_coe (measurableSet_curveBall k)).comap_apply,
    Measure.restrict_apply' (measurableSet_exhaustPiece hB k)]

instance (μ : Measure (Vec d)) [IsFiniteMeasure μ] (B : Set (Vec d)) (k : ℕ) :
    IsFiniteMeasure (pieceMeasure μ B k) :=
  ⟨by rw [pieceMeasure, (MeasurableEmbedding.subtype_coe (measurableSet_curveBall k)).comap_apply]
      exact measure_lt_top _ _⟩

/-- For the maximal `A₀` and `B = A₀ᶜ`, alternative (ii)
of `rainwater_prop` fails for `μ_k = μ⌞(B ∩ B(k))` on `B(k+1)`, `Y = 𝒢_k`, `Φ(γ) = λ_γ`; so
alternative (i) holds. -/
theorem exhaust_alt_i {e : Vec d} {α : ℝ} {μ : Measure (Vec d)} [IsFiniteMeasure μ]
    {A₀ : Set (Vec d)} (hA₀ : IsExhaustible e α μ A₀)
    (hmax : ∀ A, IsExhaustible e α μ A → μ A ≤ μ A₀) (k : ℕ) :
    ∃ E : Set (curveBall d k), MeasurableSet E ∧ pieceMeasure μ A₀ᶜ k Eᶜ = 0 ∧
      ∀ y, (curveLawK e α k y : Measure (curveBall d k)) E = 0 := by
  rcases rainwater_prop (continuous_curveLawK e α k) (pieceMeasure μ A₀ᶜ k) with
    ⟨E, hE, h0, hy⟩ | ⟨τ, E, hE, hne, hac⟩
  · exact ⟨E, hE, h0, hy⟩
  exfalso
  classical
  set B : Set (Vec d) := A₀ᶜ with hBdef
  have hBm : MeasurableSet B := hA₀.1.compl
  set P := exhaustPiece B k with hP
  have hPm : MeasurableSet P := measurableSet_exhaustPiece hBm k
  set μk := pieceMeasure μ B k with hμk
  set m : Measure (curveBall d k) := mixMeasure (curveLawK e α k) (τ : Measure _) with hm
  have : IsProbabilityMeasure m := isProbabilityMeasure_mixMeasure (continuous_curveLawK e α k) τ
  set ν : Measure (curveBall d k) := m.restrict E with hν
  set ρ : curveBall d k → ℝ≥0∞ := ν.rnDeriv μk with hρ
  have hρm : Measurable ρ := Measure.measurable_rnDeriv _ _
  set Z : Set (curveBall d k) := {x | 0 < ρ x} with hZdef
  have hνapp : ∀ s, MeasurableSet s → ν s = ∫⁻ x in s, ρ x ∂μk := by
    intro s hs
    have hwd := Measure.withDensity_rnDeriv_eq ν μk hac
    conv_lhs => rw [← hwd]
    exact withDensity_apply _ hs
  have hZ : MeasurableSet Z := measurableSet_lt measurable_const hρm
  have hZim : MeasurableSet (Subtype.val '' Z) := (measurableSet_curveBall k).subtype_image hZ
  set A'' : Set (Vec d) := Subtype.val '' Z ∩ P with hA''
  have hA''m : MeasurableSet A'' := hZim.inter hPm
  have hA''B : A'' ⊆ B := fun x hx => hx.2.1
  -- `μ(A'') ≠ 0`
  have hpos : μ A'' ≠ 0 := by
    intro h0
    have hμZ : μk Z = 0 := by rw [hμk, pieceMeasure_apply μ hBm]; exact h0
    have hνZ : ν Z = 0 := hac hμZ
    have hνZc : ν Zᶜ = 0 := by
      rw [hνapp _ hZ.compl]
      rw [setLIntegral_congr_fun hZ.compl (g := fun _ => 0) (fun x hx => by
        have : ¬ 0 < ρ x := hx
        exact nonpos_iff_eq_zero.1 (not_lt.1 this))]
      simp
    have : ν univ = 0 := by
      rw [← measure_add_measure_compl hZ, hνZ, hνZc, add_zero]
    exact hne (Measure.measure_univ_eq_zero.1 this)
  -- the measure `ρ''` on `𝒢(C)`
  let incl : ccurveSpaceK e α k → ccurveSpace e α := Set.inclusion (ccurveSpaceK_subset e α k)
  have hincl : Measurable incl := (continuous_inclusion (ccurveSpaceK_subset e α k)).measurable
  let ρ'' : Measure (ccurveSpace e α) := Measure.map incl (τ : Measure _)
  have hmix : ∀ E' : Set (Vec d), MeasurableSet E' →
      curveMix (ccurveSpace e α) ρ'' E' = m (Subtype.val ⁻¹' E') := by
    intro E' hE'
    rw [curveMix_apply _ _ hE', lintegral_map (measurable_curveLaw_apply _ hE') hincl]
    have h1 := map_val_mixMeasure_curveLawK e α k (τ : Measure _)
    have h2 := congrArg (fun q : Measure (Vec d) => q E') h1
    simp only [Measure.map_apply continuous_subtype_val.measurable hE',
      curveMix_apply _ _ hE'] at h2
    rw [hm, h2]
  have hac'' : μ.restrict A'' ≪ curveMix (ccurveSpace e α) ρ'' := by
    intro E0 hE0
    set T := toMeasurable (curveMix (ccurveSpace e α) ρ'') E0 with hT
    have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
    have hT0 : curveMix (ccurveSpace e α) ρ'' T = 0 := by rw [hT, measure_toMeasurable]; exact hE0
    have hs : MeasurableSet (Subtype.val ⁻¹' T : Set (curveBall d k)) := continuous_subtype_val.measurable hTm
    have hmT : m (Subtype.val ⁻¹' T) = 0 := by rw [← hmix T hTm]; exact hT0
    have hνT : ν (Subtype.val ⁻¹' T) = 0 :=
      nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 Measure.restrict_le_self _).trans hmT.le)
    rw [hνapp _ hs] at hνT
    have hae : ∀ᵐ x ∂μk.restrict (Subtype.val ⁻¹' T), ρ x = 0 :=
      (lintegral_eq_zero_iff hρm).1 hνT
    rw [ae_restrict_iff' hs] at hae
    have hZs : μk (Z ∩ Subtype.val ⁻¹' T) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
      exact fun h => absurd (h hx.2) (ne_of_gt hx.1)
    rw [hμk, pieceMeasure_apply μ hBm, Set.image_inter_preimage] at hZs
    refine measure_mono_null (subset_toMeasurable (curveMix (ccurveSpace e α) ρ'') E0) ?_
    rw [← hT, Measure.restrict_apply' hA''m]
    refine measure_mono_null (fun x hx => ?_) hZs
    exact ⟨⟨hx.2.1, hx.1⟩, hx.2.2⟩
  obtain ⟨hmeas0, ρ0, hρ0, hac0⟩ := hA₀
  have hfin'' : IsFiniteMeasure ρ'' := inferInstance
  have hex : IsExhaustible e α μ (A₀ ∪ A'') := by
    refine ⟨hmeas0.union hA''m, ρ0 + ρ'', inferInstance, ?_⟩
    refine (Measure.absolutelyContinuous_of_le (Measure.restrict_union_le A₀ A'')).trans
      (Measure.AbsolutelyContinuous.add_left ?_ ?_)
    · exact hac0.trans (curveMix_absolutelyContinuous _
        (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)))
    · exact hac''.trans (curveMix_absolutelyContinuous _
        (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)))
  have hle := hmax _ hex
  have hdisj : Disjoint A₀ A'' := Set.disjoint_left.2 fun x hx hx' => hA''B hx' hx
  rw [measure_union hdisj hA''m] at hle
  exact absurd hle (not_le.2 (ENNReal.lt_add_right (measure_ne_top _ _) hpos))
