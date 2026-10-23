module

public import AFree.Curves.Clamp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# `C¹` arcs are locally `C`-curves

If `γ` is `C¹` and `γ'(s)` lies in the interior of the cone, then short pieces of `γ` are `C`-curves.
-/

@[expose] public section

open MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

private lemma intCone_subset_cone (e : Vec d) (α : ℝ) : intCone e α ⊆ cone e α :=
  fun v (h : Real.cos α * vecEuclideanNorm v < vecDot v e) =>
    (le_of_lt h : Real.cos α * vecEuclideanNorm v ≤ vecDot v e)

private lemma isOpen_intCone (e : Vec d) (α : ℝ) : IsOpen (intCone e α) :=
  isOpen_lt (continuous_const.mul continuous_vecEuclideanNorm) (continuous_vecDot_left e)

/-- Let `γ` be `C¹` on an open set `J ⊆ ℝ` (e.g. `IsC1Arc γ J`) and
`O_C = {s ∈ J : γ'(s) ∈ int C(e, α)}`. Then `O_C` is open; `γ([a, b])` is a `C`-curve for every
`[a, b] ⊆ O_C`; `O_C` is the union of the compact intervals `[p, q] ⊆ O_C` with rational
endpoints; and `𝓗¹(N ∩ γ(O_C)) = 0` for every `C(e, α)`-null `N`. -/
theorem arc_ccurve {e : Vec d} {α : ℝ} {γ : ℝ → Vec d} {J : Set ℝ} (hJ : IsOpen J)
    (hγ : ContDiffOn ℝ 1 γ J) :
    IsOpen (J ∩ deriv γ ⁻¹' intCone e α) ∧
    (∀ a b : ℝ, a ≤ b → Icc a b ⊆ J ∩ deriv γ ⁻¹' intCone e α →
      IsCCurve (cone e α) (γ '' Icc a b)) ∧
    J ∩ deriv γ ⁻¹' intCone e α =
      ⋃ p : {p : ℚ × ℚ // Icc (p.1 : ℝ) p.2 ⊆ J ∩ deriv γ ⁻¹' intCone e α},
        Icc (p.1.1 : ℝ) p.1.2 ∧
    ∀ N : Set (Vec d), IsCNull (cone e α) N →
      euclideanHausdorffOne d (N ∩ γ '' (J ∩ deriv γ ⁻¹' intCone e α)) = 0 := by
  have hopen : IsOpen (J ∩ deriv γ ⁻¹' intCone e α) :=
    (hγ.continuousOn_deriv_of_isOpen hJ le_rfl).isOpen_inter_preimage hJ (isOpen_intCone e α)
  have hcurve : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ J ∩ deriv γ ⁻¹' intCone e α →
      IsCCurve (cone e α) (γ '' Icc a b) := by
    intro a b hab hsub
    obtain ⟨K, hK⟩ := (hγ.mono (fun x hx => (hsub hx).1)).exists_lipschitzOnWith one_ne_zero
      (convex_Icc a b) isCompact_Icc
    exact isCCurve_of_lipschitzOn hab hK
      (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => intCone_subset_cone e α (hsub hs).2)
  have hunion : J ∩ deriv γ ⁻¹' intCone e α =
      ⋃ p : {p : ℚ × ℚ // Icc (p.1 : ℝ) p.2 ⊆ J ∩ deriv γ ⁻¹' intCone e α},
        Icc (p.1.1 : ℝ) p.1.2 := by
    apply Subset.antisymm
    · intro s hs
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen s hs
      obtain ⟨q₁, hq₁, hq₁'⟩ := exists_rat_btwn (show s - ε < s by linarith)
      obtain ⟨q₂, hq₂, hq₂'⟩ := exists_rat_btwn (show s < s + ε by linarith)
      refine mem_iUnion.mpr ⟨⟨(q₁, q₂), fun x hx => hball ?_⟩, ⟨hq₁'.le, hq₂.le⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> simp only at hx <;> linarith [hx.1, hx.2]
    · exact iUnion_subset fun p => p.2
  refine ⟨hopen, hcurve, hunion, fun N hN => ?_⟩
  rw [hunion, image_iUnion, inter_iUnion]
  refine measure_iUnion_null fun p => ?_
  by_cases hp : (p.1.1 : ℝ) ≤ p.1.2
  · exact hN _ (hcurve _ _ hp p.2)
  · rw [Icc_eq_empty hp]; simp

end AFree
