module

public import AFree.Curves.GraphFormNull

/-!
# Gluing of `tan α`-Lipschitz graph functions

Elementary operations on `IsConeGraphFn` used for the function `g`: agreement on an interval, gluing
two pieces at a common endpoint, and the decomposition `x = (x ⬝ e) e + x_W`.
-/

@[expose] public section

open MeasureTheory Set

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ}

lemma IsConeGraphFn.congr {a b : ℝ} {η η' : ℝ → Vec d} (h : IsConeGraphFn e α a b η)
    (hη : ∀ u ∈ Icc a b, η u = η' u) : IsConeGraphFn e α a b η' :=
  ⟨fun u hu => by rw [← hη u hu]; exact h.1 u hu,
    fun u hu u' hu' => by rw [← hη u hu, ← hη u' hu']; exact h.2 u hu u' hu'⟩

private lemma graph_glue_aux {a b b' : ℝ} {η : ℝ → Vec d} (h1 : IsConeGraphFn e α a b η)
    (h2 : IsConeGraphFn e α b b' η) {u u' : ℝ} (hu : u ∈ Icc a b) (hu' : u' ∈ Icc b b') :
    vecEuclideanNorm (η u - η u') ≤ Real.tan α * |u - u'| := by
  have hb1 : b ∈ Icc a b := ⟨hu.1.trans hu.2, le_rfl⟩
  have hb2 : b ∈ Icc b b' := ⟨le_rfl, hu'.1.trans hu'.2⟩
  have e1 := h1.2 u hu b hb1
  have e2 := h2.2 b hb2 u' hu'
  have : η u - η u' = (η u - η b) + (η b - η u') := by abel
  rw [this]
  refine (vecEuclideanNorm_add_le _ _).trans ?_
  have hn : Real.tan α * |u - b| + Real.tan α * |b - u'| = Real.tan α * |u - u'| := by
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu'.1]),
      abs_of_nonpos (by linarith [hu.2, hu'.1])]
    ring
  linarith

/-- Gluing two `tan α`-Lipschitz graph functions at a common endpoint. -/
lemma IsConeGraphFn.glue {a b b' : ℝ} {η : ℝ → Vec d}
    (h1 : IsConeGraphFn e α a b η) (h2 : IsConeGraphFn e α b b' η) :
    IsConeGraphFn e α a b' η := by
  have hsub : ∀ u ∈ Icc a b', u ∈ Icc a b ∨ u ∈ Icc b b' := by
    intro u hu
    rcases le_total u b with h | h
    · exact Or.inl ⟨hu.1, h⟩
    · exact Or.inr ⟨h, hu.2⟩
  refine ⟨fun u hu => ?_, fun u hu u' hu' => ?_⟩
  · rcases hsub u hu with h | h
    · exact h1.1 u h
    · exact h2.1 u h
  · rcases hsub u hu with h | h <;> rcases hsub u' hu' with h' | h'
    · exact h1.2 u h u' h'
    · exact graph_glue_aux h1 h2 h h'
    · rw [vecEuclideanNorm_sub_comm, abs_sub_comm]; exact graph_glue_aux h1 h2 h' h
    · exact h2.2 u h u' h'

/-- Replace `η` by `ζ` after the common point `b`. -/
lemma IsConeGraphFn.extend {a b b' : ℝ} {η ζ : ℝ → Vec d}
    (h1 : IsConeGraphFn e α a b η) (h2 : IsConeGraphFn e α b b' ζ) (hη : η b = ζ b) :
    IsConeGraphFn e α a b' (fun u => if u ≤ b then η u else ζ u) := by
  refine IsConeGraphFn.glue (h1.congr fun u hu => by simp [hu.2]) (h2.congr fun u hu => ?_)
  by_cases hub : u ≤ b
  · have : u = b := le_antisymm hub hu.1
    subst this; simp [hη]
  · simp [hub]

/-- A constant (orthogonal to `e`) is a graph function. -/
lemma isConeGraphFn_const (hα : 0 ≤ Real.tan α) (a b : ℝ)
    {w : Vec d} (hw : vecDot w e = 0) : IsConeGraphFn e α a b (fun _ => w) :=
  ⟨fun _ _ => hw, fun u _ u' _ => by
    have h0 : vecEuclideanNorm ((fun _ => w) u - (fun _ => w) u') = 0 :=
      vecEuclideanNorm_eq_zero_iff.mpr (sub_self w)
    rw [h0]; exact mul_nonneg hα (abs_nonneg _)⟩

/-- A `tan α`-Lipschitz graph function is Lipschitz on `[a, b]` for the sup metric. -/
lemma IsConeGraphFn.lipschitzOnWith {a b : ℝ} {η : ℝ → Vec d} (hα : 0 ≤ Real.tan α)
    (h : IsConeGraphFn e α a b η) :
    LipschitzOnWith (Real.toNNReal (Real.tan α)) η (Icc a b) := by
  refine LipschitzOnWith.of_dist_le_mul fun u hu u' hu' => ?_
  rw [dist_eq_norm, Real.coe_toNNReal _ hα, Real.dist_eq]
  exact (norm_le_vecEuclideanNorm _).trans (h.2 u hu u' hu')

lemma IsConeGraphFn.continuousOn_graphCurve {a b : ℝ} {η : ℝ → Vec d} (hα : 0 ≤ Real.tan α)
    (h : IsConeGraphFn e α a b η) : ContinuousOn (graphCurve e η) (Icc a b) :=
  (continuousOn_id.smul continuousOn_const).add (h.lipschitzOnWith hα).continuousOn

end AFree
