module

public import AFree.Curves.Rainwater.GkTop

/-!
# The measures `λ_γ` and `[ρ]`
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- `λ_γ = γ_# 𝓛¹⌞[0,1]`, a probability measure on `ℝ^d`. -/
noncomputable def curveLaw (γ : C(I, Vec d)) : Measure (Vec d) := Measure.map γ volume

/-- `[ρ] = Θ_ρ = ev_#(ρ ⊗ 𝓛¹⌞[0,1])` for a measure `ρ` on a set `S` of paths
(typically `S = 𝒢(C)`), a finite measure on `ℝ^d` of total mass `ρ(S)`. -/
noncomputable def curveMix (S : Set C(I, Vec d)) (ρ : Measure S) : Measure (Vec d) :=
  Measure.map (fun p : S × I => (p.1 : C(I, Vec d)) p.2) (ρ.prod volume)

lemma curveLaw_apply (γ : C(I, Vec d)) {E : Set (Vec d)} (hE : MeasurableSet E) :
    curveLaw γ E = volume (γ ⁻¹' E) :=
  Measure.map_apply γ.continuous.measurable hE

private lemma measurable_evalPair (S : Set C(I, Vec d)) :
    Measurable fun p : S × I => (p.1 : C(I, Vec d)) p.2 :=
  (continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)).measurable

/-- `γ ↦ λ_γ(E)` is Borel for Borel `E` (Tonelli). -/
lemma measurable_curveLaw_apply (S : Set C(I, Vec d)) {E : Set (Vec d)} (hE : MeasurableSet E) :
    Measurable fun γ : S => curveLaw (γ : C(I, Vec d)) E := by
  have h : Measurable fun γ : S => volume (Prod.mk γ ⁻¹'
      ((fun p : S × I => (p.1 : C(I, Vec d)) p.2) ⁻¹' E)) :=
    measurable_measure_prodMk_left ((measurable_evalPair S) hE)
  have : (fun γ : S => curveLaw (γ : C(I, Vec d)) E) = fun γ : S => volume (Prod.mk γ ⁻¹'
      ((fun p : S × I => (p.1 : C(I, Vec d)) p.2) ⁻¹' E)) := by
    funext γ
    rw [curveLaw_apply _ hE]
    rfl
  rw [this]
  exact h

/-- `[ρ](E) = ∫ λ_γ(E) dρ(γ)` for Borel `E`. -/
lemma curveMix_apply (S : Set C(I, Vec d)) (ρ : Measure S) {E : Set (Vec d)}
    (hE : MeasurableSet E) :
    curveMix S ρ E = ∫⁻ γ, curveLaw (γ : C(I, Vec d)) E ∂ρ := by
  rw [curveMix, Measure.map_apply (measurable_evalPair S) hE, Measure.prod_apply
    ((measurable_evalPair S) hE)]
  refine lintegral_congr fun γ => ?_
  rw [curveLaw_apply _ hE]
  rfl

end AFree
