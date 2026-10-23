module

public import AFree.Curves.Exhaust.CurrentDef
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Borel measurability and cone property of the derivative `D(γ, s)`
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

lemma continuous_curveExtUncurry (e : Vec d) (α : ℝ) :
    Continuous (Function.uncurry fun (γ : ccurveSpace e α) (s : ℝ) =>
      ccurveExt (γ : C(I, Vec d)) s) := by
  have h : Continuous fun p : ccurveSpace e α × ℝ =>
      ((p.1 : C(I, Vec d)), Set.projIcc (0 : ℝ) 1 zero_le_one p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_projIcc.comp continuous_snd)
  exact continuous_eval.comp h

/-- `D` is Borel on `𝒢(C) × [0,1]`. -/
lemma measurable_curveDeriv (e : Vec d) (α : ℝ) : Measurable (curveDeriv e α) := by
  have h := measurable_deriv_with_param (𝕜 := ℝ) (continuous_curveExtUncurry e α)
  exact h.comp (measurable_fst.prodMk (continuous_subtype_val.measurable.comp measurable_snd))

private def GoodDeriv (e : Vec d) (α : ℝ) (v : Vec d) : Prop :=
  vecEuclideanNorm v ≤ 1 ∧ v ∈ cone e α ∧ Real.cos α ≤ vecDot v e

private lemma measurableSet_goodDeriv (e : Vec d) (α : ℝ) :
    MeasurableSet {p : ccurveSpace e α × I | GoodDeriv e α (curveDeriv e α p)} := by
  have hm := measurable_curveDeriv e α
  have h1 : MeasurableSet {p : ccurveSpace e α × I | vecEuclideanNorm (curveDeriv e α p) ≤ 1} :=
    measurableSet_le (Curves.continuous_vecEuclideanNorm.measurable.comp hm) measurable_const
  have h2 : MeasurableSet {p : ccurveSpace e α × I | curveDeriv e α p ∈ cone e α} :=
    (cone_isClosed e α).measurableSet.preimage hm
  have h3 : MeasurableSet {p : ccurveSpace e α × I |
      Real.cos α ≤ vecDot (curveDeriv e α p) e} :=
    measurableSet_le measurable_const ((Curves.continuous_vecDot_left e).measurable.comp hm)
  exact h1.inter (h2.inter h3)

/-- `D` is Borel on `𝒢(C) × [0,1]`; for every `γ ∈ 𝒢(C)` and
a.e. `s`, `|D(γ,s)| ≤ 1`, `D(γ,s) ∈ C` and `D(γ,s) ⬝ e ≥ cos α`; hence the same holds
`Ξ`-a.e. for `Ξ = ρ ⊗ 𝓛¹⌞[0,1]` (Tonelli). -/
theorem curveDeriv_borel {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    Measurable (curveDeriv e α) ∧
    (∀ γ : ccurveSpace e α, ∀ᵐ s ∂(volume : Measure I),
      vecEuclideanNorm (curveDeriv e α (γ, s)) ≤ 1 ∧ curveDeriv e α (γ, s) ∈ cone e α ∧
        Real.cos α ≤ vecDot (curveDeriv e α (γ, s)) e) ∧
    (∀ (ρ : Measure (ccurveSpace e α)) [SFinite ρ], ∀ᵐ p ∂(curveXi e α ρ),
      vecEuclideanNorm (curveDeriv e α p) ≤ 1 ∧ curveDeriv e α p ∈ cone e α ∧
        Real.cos α ≤ vecDot (curveDeriv e α p) e) := by
  have hfib : ∀ γ : ccurveSpace e α, ∀ᵐ s ∂(volume : Measure I),
      GoodDeriv e α (curveDeriv e α (γ, s)) := by
    intro γ
    have h := (ccurveSpace_curve_properties hα hα2 γ.2).2.2.1
    have h' := (ae_restrict_iff_subtype (μ := (volume : Measure ℝ))
      (s := Icc (0 : ℝ) 1) measurableSet_Icc).1 h
    filter_upwards [h'] with s hs
    exact ⟨hs.2.1, hs.2.2.2, hs.2.2.1⟩
  refine ⟨measurable_curveDeriv e α, hfib, fun ρ _ => ?_⟩
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_goodDeriv e α)).2
    (ae_of_all _ hfib)

end AFree
