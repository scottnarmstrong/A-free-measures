module

public import AFree.Defs

/-!
# Cones, `C`-curves and `C`-null sets

Following [AM, Section 4.9], `C`-curves are Lipschitz curves with derivative in `C` almost everywhere.
Points are `Vec d`; Euclidean quantities use `vecEuclideanNorm` and `vecDot`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace AFree

open PDE

/-- The cone `C(e, α) = {v : v ⬝ e ≥ cos α · |v|}` (Euclidean norm and dot product). -/
def cone {d : ℕ} (e : Vec d) (α : ℝ) : Set (Vec d) :=
  {v | Real.cos α * vecEuclideanNorm v ≤ vecDot v e}

/-- The open cone `int C(e, α) = {v : v ⬝ e > cos α · |v|}` of the cone. -/
def intCone {d : ℕ} (e : Vec d) (α : ℝ) : Set (Vec d) :=
  {v | Real.cos α * vecEuclideanNorm v < vecDot v e}

/-- A parametrization `γ : ℝ → ℝ^d` of a `C`-curve on `[a, b]`: `γ` is Lipschitz and
`γ'(s) ∈ C` for Lebesgue-a.e. `s ∈ [a, b]` (`deriv` is the Fréchet derivative on `ℝ`). -/
def IsCCurveParam {d : ℕ} (C : Set (Vec d)) (a b : ℝ) (γ : ℝ → Vec d) : Prop :=
  (∃ K : ℝ≥0, LipschitzWith K γ) ∧ ∀ᵐ s ∂(volume.restrict (Icc a b)), deriv γ s ∈ C

/-- `G` is a `C`-curve: `G = γ([a, b])` with `a ≤ b` and `γ` Lipschitz with
`γ'(s) ∈ C` for a.e. `s ∈ [a, b]`. As usual, `γ` is defined on all of `ℝ` (replace it by
`γ ∘ clamp`); `C` is an arbitrary set, the cone being `cone e α`. -/
def IsCCurve {d : ℕ} (C : Set (Vec d)) (G : Set (Vec d)) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ ∃ γ : ℝ → Vec d, IsCCurveParam C a b γ ∧ G = γ '' Icc a b

/-- `E` is `C`-null: `𝓗¹(E ∩ G) = 0` for every `C`-curve `G`. -/
def IsCNull {d : ℕ} (C : Set (Vec d)) (E : Set (Vec d)) : Prop :=
  ∀ G, IsCCurve C G → euclideanHausdorffOne d (E ∩ G) = 0

lemma IsCNull.mono {d : ℕ} {C : Set (Vec d)} {E F : Set (Vec d)} (h : IsCNull C F) (hEF : E ⊆ F) :
    IsCNull C E := fun G hG =>
  measure_mono_null (inter_subset_inter_left _ hEF) (h G hG)

lemma isCNull_iUnion {d : ℕ} {C : Set (Vec d)} {E : ℕ → Set (Vec d)}
    (h : ∀ n, IsCNull C (E n)) : IsCNull C (⋃ n, E n) := fun G hG => by
  rw [iUnion_inter]
  exact measure_iUnion_null fun n => h n G hG

end AFree
