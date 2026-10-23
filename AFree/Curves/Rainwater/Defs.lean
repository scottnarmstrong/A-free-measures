module

public import AFree.Curves
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Analysis.Calculus.Rademacher
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# The spaces `𝒢(C)` and `𝒢_k` of normalized `C`-curves

The ambient space is `C(I, Vec d)`
(`I = [0,1]`) with the sup distance. `𝒢_k` consists of the
normalized paths *meeting* the closed Euclidean ball `B(k)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- `𝒢(C)` for `C = C(e, α)`: the maps `γ : [0,1] → ℝ^d` with
`|γ(s') - γ(s)| ≤ s' - s` and `(γ(s') - γ(s)) ⬝ e ≥ cos α · (s' - s)` for `0 ≤ s ≤ s' ≤ 1`. -/
def ccurveSpace (e : Vec d) (α : ℝ) : Set C(I, Vec d) :=
  {γ | ∀ s s' : I, s ≤ s' → vecEuclideanNorm (γ s' - γ s) ≤ (s' : ℝ) - s ∧
    Real.cos α * ((s' : ℝ) - s) ≤ vecDot (γ s' - γ s) e}

/-- `𝒢_k = {γ ∈ 𝒢(C) : ∃ s, |γ(s)| ≤ k}`, the normalized paths meeting `B(k)`. -/
def ccurveSpaceK (e : Vec d) (α : ℝ) (k : ℕ) : Set C(I, Vec d) :=
  {γ | γ ∈ ccurveSpace e α ∧ ∃ s : I, vecEuclideanNorm (γ s) ≤ k}

lemma ccurveSpaceK_subset (e : Vec d) (α : ℝ) (k : ℕ) : ccurveSpaceK e α k ⊆ ccurveSpace e α :=
  fun _ h => h.1

lemma ccurveSpace_dist_le {e : Vec d} {α : ℝ} {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpace e α)
    (s s' : I) : vecEuclideanNorm (γ s' - γ s) ≤ |(s' : ℝ) - s| := by
  rcases le_total s s' with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (show (s : ℝ) ≤ s' from h))]; exact (hγ s s' h).1
  · have := (hγ s' s h).1
    rw [abs_of_nonpos (sub_nonpos.2 (show (s' : ℝ) ≤ s from h)), neg_sub, ← vecEuclideanNorm_neg,
      neg_sub]
    exact this

lemma ccurveSpaceK_norm_le {e : Vec d} {α : ℝ} {k : ℕ} {γ : C(I, Vec d)}
    (hγ : γ ∈ ccurveSpaceK e α k) (s : I) : vecEuclideanNorm (γ s) ≤ k + 1 := by
  obtain ⟨hγ, s₀, hs₀⟩ := hγ
  have h1 := ccurveSpace_dist_le hγ s₀ s
  have h2 : |(s : ℝ) - s₀| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [s.2.1, s.2.2, s₀.2.1, s₀.2.2]
  have h3 := vecEuclideanNorm_add_le (γ s - γ s₀) (γ s₀)
  rw [sub_add_cancel] at h3
  linarith

end AFree
