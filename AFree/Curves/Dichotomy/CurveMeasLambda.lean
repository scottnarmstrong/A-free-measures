module

public import AFree.Curves.Rainwater

/-!
# The length functional `Λ_γ(U)` and its lower semicontinuity

The supremum over finite families of
intervals with disjoint interiors is written as a supremum over monotone finite sequences
`u₀ ≤ ⋯ ≤ uₙ`, each consecutive interval `[uᵢ, uᵢ₊₁]` being counted (by its chord length) when its
image lies in `U`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The chord `|γ b - γ a|` of the extended path if `γ([a,b]) ⊆ U`, and `0` otherwise. -/
noncomputable def curveGap (γ : C(I, Vec d)) (U : Set (Vec d)) (a b : ℝ) : ℝ≥0∞ :=
  open scoped Classical in
  if ccurveExt γ '' Icc a b ⊆ U then
    ENNReal.ofReal (vecEuclideanNorm (ccurveExt γ b - ccurveExt γ a)) else 0

/-- `Λ_γ(U)` (restricted to partitions with nodes in `s`): the supremum of the sums of the chords
of the consecutive intervals of a partition whose image lies in `U`. -/
noncomputable def curveLambda (γ : C(I, Vec d)) (U : Set (Vec d)) (s : Set ℝ) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range p.1, curveGap γ U (p.2.1 i) (p.2.1 (i + 1))

lemma ccurveExt_image_eq (γ : C(I, Vec d)) (a b : ℝ) :
    ccurveExt γ '' Icc a b = γ '' (Set.projIcc (0 : ℝ) 1 zero_le_one '' Icc a b) := by
  rw [← image_comp]
  rfl

lemma isOpen_mapsTo_ccurveExt {U : Set (Vec d)} (hU : IsOpen U) (a b : ℝ) :
    IsOpen {γ : C(I, Vec d) | ccurveExt γ '' Icc a b ⊆ U} := by
  have hK : IsCompact (Set.projIcc (0 : ℝ) 1 zero_le_one '' Icc a b) :=
    isCompact_Icc.image (continuous_projIcc)
  have := ContinuousMap.isOpen_setOfPred_mapsTo (X := I) (Y := Vec d) hK hU
  convert this using 2
  ext γ
  rw [ccurveExt_image_eq]
  exact image_subset_iff

lemma continuous_ccurveExt_eval (x : ℝ) : Continuous fun γ : C(I, Vec d) => ccurveExt γ x :=
  continuous_eval_const (Set.projIcc (0 : ℝ) 1 zero_le_one x)

lemma lowerSemicontinuous_curveGap {U : Set (Vec d)} (hU : IsOpen U) (a b : ℝ) :
    LowerSemicontinuous fun γ : C(I, Vec d) => curveGap γ U a b := by
  intro γ₀ y hy
  unfold curveGap at hy ⊢
  beta_reduce at hy ⊢
  by_cases h : ccurveExt γ₀ '' Icc a b ⊆ U
  · simp only [h, ↓reduceIte] at hy
    have hc : Continuous fun γ : C(I, Vec d) =>
        ENNReal.ofReal (vecEuclideanNorm (ccurveExt γ b - ccurveExt γ a)) :=
      ENNReal.continuous_ofReal.comp (PDE.continuous_vecEuclideanNorm.comp
        ((continuous_ccurveExt_eval b).sub (continuous_ccurveExt_eval a)))
    have h1 := (hc.tendsto γ₀).eventually (lt_mem_nhds hy)
    filter_upwards [h1, (isOpen_mapsTo_ccurveExt hU a b).mem_nhds h] with γ h1 h2
    simp only [h2, ↓reduceIte]
    exact h1
  · simp only [h, ↓reduceIte] at hy
    exact absurd hy (not_lt.2 zero_le)

/-- For `U` open, `γ ↦ Λ_γ(U)` is lower semicontinuous on
`C([0,1], ℝ^d)` (uniform convergence), hence Borel. -/
theorem lowerSemicontinuous_curveLambda {U : Set (Vec d)} (hU : IsOpen U) (s : Set ℝ) :
    LowerSemicontinuous fun γ : C(I, Vec d) => curveLambda γ U s :=
  lowerSemicontinuous_iSup fun _ =>
    lowerSemicontinuous_sum fun _ _ => lowerSemicontinuous_curveGap hU _ _

theorem measurable_curveLambda {U : Set (Vec d)} (hU : IsOpen U) (s : Set ℝ) :
    Measurable fun γ : C(I, Vec d) => curveLambda γ U s :=
  (lowerSemicontinuous_curveLambda hU s).measurable

end AFree
