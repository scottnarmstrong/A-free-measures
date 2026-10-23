module

public import AFree.Curves.Dichotomy.CurveMeasUpper
public import Mathlib.MeasureTheory.PiSystem

/-!
# Borel dependence of `𝓗¹⌞γ([0,1])` on `γ`

Length formula on open sets, lower
semicontinuity, then a Dynkin (monotone class) argument.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- For `γ ∈ 𝒢(C)` and `U` open,
`𝓗¹(U ∩ γ([0,1])) = Λ_γ(U)`. -/
theorem hausdorffOne_inter_range_eq_curveLambda {e : Vec d} {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpace e α) {U : Set (Vec d)}
    (hU : IsOpen U) :
    euclideanHausdorffOne d (U ∩ range γ) = curveLambda γ U (Icc 0 1) :=
  le_antisymm (hausdorffOne_inter_range_le hγ hU) (curveLambda_le hα hα2 hγ U)

/-- The map `γ ↦ 𝓗¹(U ∩ γ([0,1]))` is Borel on `𝒢(C)` for `U` open. -/
theorem measurable_hausdorffOne_inter_range_of_isOpen {e : Vec d} {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {U : Set (Vec d)} (hU : IsOpen U) :
    Measurable fun γ : ccurveSpace e α => euclideanHausdorffOne d (U ∩ range (γ : C(I, Vec d))) := by
  have : (fun γ : ccurveSpace e α => euclideanHausdorffOne d (U ∩ range (γ : C(I, Vec d)))) =
      fun γ : ccurveSpace e α => curveLambda (γ : C(I, Vec d)) U (Icc 0 1) :=
    funext fun γ => hausdorffOne_inter_range_eq_curveLambda hα hα2 γ.2 hU
  rw [this]
  exact (measurable_curveLambda hU _).comp measurable_subtype_coe

/-- The Borel sets `B` for which `γ ↦ 𝓗¹(B ∩ γ([0,1]))` is Borel on
`𝒢(C)` form a Dynkin system containing the open sets, hence all Borel sets. -/
theorem measurable_hausdorffOne_inter_range_dynkin {e : Vec d} (he : vecEuclideanNorm e = 1)
    {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2) {B : Set (Vec d)} (hB : MeasurableSet B) :
    Measurable fun γ : ccurveSpace e α => euclideanHausdorffOne d (B ∩ range (γ : C(I, Vec d))) := by
  have hfin : ∀ γ : ccurveSpace e α, euclideanHausdorffOne d (range (γ : C(I, Vec d))) ≠ ⊤ := by
    intro γ
    have h := ((ccurveSpace_measure_comparison he hα hα2 γ.2).2 univ).1
    simp only [univ_inter, preimage_univ, measure_univ] at h
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h
  have hR : ∀ γ : ccurveSpace e α, MeasurableSet (range (γ : C(I, Vec d))) := fun γ =>
    (isCompact_range (γ : C(I, Vec d)).continuous).measurableSet
  refine MeasurableSpace.induction_on_inter
    (C := fun B _ => Measurable fun γ : ccurveSpace e α =>
      euclideanHausdorffOne d (B ∩ range (γ : C(I, Vec d))))
    (BorelSpace.measurable_eq (α := Vec d)) isPiSystem_isOpen ?_ ?_ ?_ ?_ B hB
  · simp
  · intro U hU
    exact measurable_hausdorffOne_inter_range_of_isOpen hα hα2 hU
  · intro B hB ih
    have key : ∀ γ : ccurveSpace e α, euclideanHausdorffOne d (Bᶜ ∩ range (γ : C(I, Vec d))) =
        euclideanHausdorffOne d (range (γ : C(I, Vec d))) -
          euclideanHausdorffOne d (B ∩ range (γ : C(I, Vec d))) := by
      intro γ
      refine ENNReal.eq_sub_of_add_eq ?_ ?_
      · exact ne_top_of_le_ne_top (hfin γ) (measure_mono inter_subset_right)
      · have := measure_inter_add_sdiff (μ := euclideanHausdorffOne d)
          (range (γ : C(I, Vec d))) hB
        rw [sdiff_eq] at this
        rw [add_comm, inter_comm B, inter_comm Bᶜ]
        exact this
    simp_rw [key]
    have huniv : Measurable fun γ : ccurveSpace e α =>
        euclideanHausdorffOne d (range (γ : C(I, Vec d))) := by
      simpa using measurable_hausdorffOne_inter_range_of_isOpen (e := e) hα hα2 isOpen_univ
    exact huniv.sub ih
  · intro f hdisj hfm ih
    have key : ∀ γ : ccurveSpace e α,
        euclideanHausdorffOne d ((⋃ i, f i) ∩ range (γ : C(I, Vec d))) =
          ∑' i, euclideanHausdorffOne d (f i ∩ range (γ : C(I, Vec d))) := by
      intro γ
      rw [iUnion_inter]
      exact measure_iUnion (fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left)
        fun i => (hfm i).inter (hR γ)
    simp_rw [key]
    exact Measurable.tsum ih

/-- For Borel `B ⊆ ℝ^d` the map `γ ↦ 𝓗¹(B ∩ γ([0,1]))` is Borel on `𝒢(C)`,
`C = C(e, α)`. -/
theorem measurable_hausdorffOne_inter_range {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ}
    (hα : 0 < α) (hα2 : α < Real.pi / 2) {B : Set (Vec d)} (hB : MeasurableSet B) :
    Measurable fun γ : ccurveSpace e α => euclideanHausdorffOne d (B ∩ Set.range (γ : C(I, Vec d))) :=
  measurable_hausdorffOne_inter_range_dynkin he hα hα2 hB

end AFree
