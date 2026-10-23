module

public import AFree.Curves.Clamp
public import AFree.Curves.HausdorffLip

/-!
# Graph form of `C`-curves

A `t`-Lipschitz map `η : [u₀, u₁] → e^⊥`
(Euclidean norm, `t = tan α`) gives the graph curve `γ_η(u) = u e + η(u)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- The graph curve `γ_η(u) = u e + η(u)`. -/
def graphCurve (e : Vec d) (η : ℝ → Vec d) (u : ℝ) : Vec d := u • e + η u

/-- `η : [u₀, u₁] → e^⊥` is `tan α`-Lipschitz for the Euclidean norm. -/
def IsConeGraphFn (e : Vec d) (α : ℝ) (u₀ u₁ : ℝ) (η : ℝ → Vec d) : Prop :=
  (∀ u ∈ Icc u₀ u₁, vecDot (η u) e = 0) ∧
    ∀ u ∈ Icc u₀ u₁, ∀ u' ∈ Icc u₀ u₁, vecEuclideanNorm (η u - η u') ≤ Real.tan α * |u - u'|

private lemma vecNormSq_unit {e : Vec d} (he : vecEuclideanNorm e = 1) : vecNormSq e = 1 := by
  have := vecEuclideanNorm_sq e; rw [he] at this; linarith

private lemma dot_graphCurve {e : Vec d} (he : vecEuclideanNorm e = 1) (η : ℝ → Vec d) (u : ℝ)
    (h : vecDot (η u) e = 0) : vecDot (graphCurve e η u) e = u := by
  rw [graphCurve, vecDot_add_left, vecDot_smul_left, vecDot_self, vecNormSq_unit he, h]; ring

private lemma graph_incr_mem {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {u₀ u₁ : ℝ} {η : ℝ → Vec d} (hη : IsConeGraphFn e α u₀ u₁ η)
    {u u' : ℝ} (hu : u ∈ Icc u₀ u₁) (hu' : u' ∈ Icc u₀ u₁) (huu : u ≤ u') :
    graphCurve e η u' - graphCurve e η u ∈ cone e α := by
  rw [cone_iff he hα hα2]
  have hd : vecDot (graphCurve e η u' - graphCurve e η u) e = u' - u := by
    rw [vecDot_sub_left, dot_graphCurve he η u' (hη.1 u' hu'), dot_graphCurve he η u (hη.1 u hu)]
  have hw : graphCurve e η u' - graphCurve e η u - vecDot (graphCurve e η u' - graphCurve e η u) e • e
      = η u' - η u := by
    rw [hd, graphCurve, graphCurve, sub_smul]; abel
  rw [hd] at hw
  rw [hd, hw]
  refine ⟨by linarith, ?_⟩
  have := hη.2 u' hu' u hu
  rwa [abs_of_nonneg (by linarith)] at this

private lemma graph_norm_le {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {u₀ u₁ : ℝ} {η : ℝ → Vec d} (hη : IsConeGraphFn e α u₀ u₁ η)
    {u u' : ℝ} (hu : u ∈ Icc u₀ u₁) (hu' : u' ∈ Icc u₀ u₁) :
    vecEuclideanNorm (graphCurve e η u' - graphCurve e η u) ≤ |u' - u| / Real.cos α := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  rw [le_div_iff₀ hc]
  have hd : vecDot (graphCurve e η u' - graphCurve e η u) e = u' - u := by
    rw [vecDot_sub_left, dot_graphCurve he η u' (hη.1 u' hu'), dot_graphCurve he η u (hη.1 u hu)]
  have hw : vecNormSq (η u' - η u) ≤ (Real.tan α * |u' - u|) ^ 2 := by
    have := hη.2 u' hu' u hu
    have h0 := vecEuclideanNorm_sq (η u' - η u)
    rw [← h0]; exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) this 2
  have hpy := vecNormSq_sub_dot_smul he (graphCurve e η u' - graphCurve e η u)
  have hw' : graphCurve e η u' - graphCurve e η u - vecDot (graphCurve e η u' - graphCurve e η u) e • e
      = η u' - η u := by
    rw [hd, graphCurve, graphCurve, sub_smul]; abel
  rw [hw', hd] at hpy
  have hsq : (vecEuclideanNorm (graphCurve e η u' - graphCurve e η u) * Real.cos α) ^ 2 ≤
      |u' - u| ^ 2 := by
    have h0 := vecEuclideanNorm_sq (graphCurve e η u' - graphCurve e η u)
    have ht : Real.tan α = Real.sin α / Real.cos α := Real.tan_eq_sin_div_cos α
    have hsc := Real.sin_sq_add_cos_sq α
    have : (Real.tan α * |u' - u|) ^ 2 * Real.cos α ^ 2 = Real.sin α ^ 2 * |u' - u| ^ 2 := by
      rw [ht]; field_simp
    have hu2 : (u' - u) ^ 2 = |u' - u| ^ 2 := (sq_abs _).symm
    rw [mul_pow, h0]
    nlinarith [sq_nonneg (Real.cos α), mul_le_mul_of_nonneg_right hw (sq_nonneg (Real.cos α))]
  exact le_of_sq_le_sq (by simpa using hsq) (abs_nonneg _)

/-- For `η` `tan α`-Lipschitz into `e^⊥`
on `[u₀, u₁]`: `γ_η` is `1/cos α`-Lipschitz, has increments in `C(e, α)`, is injective, satisfies
`e ⬝ γ_η(u) = u`, and `γ_η([u₀, u₁])` is a `C`-curve. -/
theorem graphCurve_isCCurve {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {u₀ u₁ : ℝ} (hu : u₀ ≤ u₁) {η : ℝ → Vec d}
    (hη : IsConeGraphFn e α u₀ u₁ η) :
    (∀ u ∈ Icc u₀ u₁, ∀ u' ∈ Icc u₀ u₁,
        vecEuclideanNorm (graphCurve e η u' - graphCurve e η u) ≤ |u' - u| / Real.cos α) ∧
      (∀ u ∈ Icc u₀ u₁, ∀ u' ∈ Icc u₀ u₁, u ≤ u' →
        graphCurve e η u' - graphCurve e η u ∈ cone e α) ∧
      InjOn (graphCurve e η) (Icc u₀ u₁) ∧
      (∀ u ∈ Icc u₀ u₁, vecDot (graphCurve e η u) e = u) ∧
      IsCCurve (cone e α) (graphCurve e η '' Icc u₀ u₁) := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hdot : ∀ u ∈ Icc u₀ u₁, vecDot (graphCurve e η u) e = u :=
    fun u hu => dot_graphCurve he η u (hη.1 u hu)
  have hnorm := fun u (hu : u ∈ Icc u₀ u₁) u' (hu' : u' ∈ Icc u₀ u₁) =>
    graph_norm_le he hα hα2 hη hu hu'
  have hinc := fun u (hu : u ∈ Icc u₀ u₁) u' (hu' : u' ∈ Icc u₀ u₁) (h : u ≤ u') =>
    graph_incr_mem he hα hα2 hη hu hu' h
  refine ⟨hnorm, hinc, ?_, hdot, ?_⟩
  · intro u hu u' hu' h
    rw [← hdot u hu, ← hdot u' hu', h]
  · have hlip : LipschitzOnWith (Real.toNNReal (1 / Real.cos α)) (graphCurve e η) (Icc u₀ u₁) := by
      refine LipschitzOnWith.of_dist_le_mul fun u hu u' hu' => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), Real.norm_eq_abs]
      refine (norm_le_vecEuclideanNorm _).trans ((hnorm u' hu' u hu).trans (le_of_eq ?_))
      ring
    exact isCCurve_of_lipschitzOn hu hlip ((ccurve_incr_iff (e := e) hα hα2 hu hlip).mpr hinc)

end AFree
