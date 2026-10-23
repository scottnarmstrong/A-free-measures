module

public import AFree.Curves.Rainwater
public import AFree.Defs
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# The curve current `N_ρ` (definition)

For a measure `ρ` on
`𝒢(C)` put `Ξ = ρ ⊗ 𝓛¹⌞[0,1]`, `D(γ, s) = deriv γ̄ s` (junk value `0`) and
`N_ρ = (Ξ.withDensityᵥ D̃).map ev` with `D̃(γ, s)(⟨{j}, _⟩) = D(γ, s)_j`.
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- `D(γ, s) = deriv γ̄ s ∈ ℝ^d`, `γ̄` the constant extension of `γ ∈ 𝒢(C)` to `ℝ`. -/
noncomputable def curveDeriv (e : Vec d) (α : ℝ) (p : ccurveSpace e α × I) : Vec d :=
  deriv (ccurveExt (p.1 : C(I, Vec d))) (p.2 : ℝ)

/-- A vector of `ℝ^d` as a `1`-vector (`v ↦ Σ_j v_j e_{{j}}`, coordinate `{j} ↦ v_j`). -/
def vecToKVecOne (v : Vec d) : KVec d 1 := fun K => ∑ j ∈ K.1, v j

lemma vecToKVecOne_apply (v : Vec d) (j : Fin d) :
    vecToKVecOne v ⟨{j}, Finset.card_singleton j⟩ = v j := by
  simp [vecToKVecOne]

/-- The evaluation `(γ, s) ↦ γ(s)` on `𝒢(C) × [0,1]`. -/
def curveEval (e : Vec d) (α : ℝ) (p : ccurveSpace e α × I) : Vec d :=
  (p.1 : C(I, Vec d)) p.2

/-- `Ξ = ρ ⊗ 𝓛¹⌞[0,1]` on `𝒢(C) × [0,1]`. -/
noncomputable def curveXi (e : Vec d) (α : ℝ) (ρ : Measure (ccurveSpace e α)) :
    Measure (ccurveSpace e α × I) := ρ.prod volume

/-- The curve current `N_ρ = (Ξ.withDensityᵥ D̃).map ev` as a `KVec d 1`-valued vector measure
on `ℝ^d`, `N_ρ(B)_j = ∫∫ 1_B(γ(s)) D(γ, s)_j ds dρ(γ)`. -/
noncomputable def curveCurrent (e : Vec d) (α : ℝ) (ρ : Measure (ccurveSpace e α)) :
    VectorMeasure (Vec d) (KVec d 1) :=
  ((curveXi e α ρ).withDensityᵥ fun p => vecToKVecOne (curveDeriv e α p)).map (curveEval e α)

end AFree
