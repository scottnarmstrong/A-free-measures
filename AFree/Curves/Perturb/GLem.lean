module

public import AFree.Curves.Perturb.GLip

/-!
# The Lipschitz function `g` of [AM, Proposition 7.4]
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ} {A : Set (Vec d)} {ε : ℝ}

private lemma perturbG_abs_smul (he : vecEuclideanNorm e = 1) (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (hε : 0 ≤ ε)
    (hA : ∀ a b η, IsConeGraphFn e α a b η → perturbMeas e A a b η ≤ ENNReal.ofReal ε)
    (y : Vec d) (s : ℝ) : |perturbG e α A (y + s • e) - perturbG e α A y| ≤ |s| := by
  rcases le_total 0 s with hs | hs
  · have := perturbG_monotone he hα hα2 hε hA y hs
    rw [abs_of_nonneg hs, abs_le]; constructor <;> linarith [this.1, this.2.1]
  · have := perturbG_monotone he hα hα2 hε hA (y + s • e) (s := -s) (by linarith)
    have hy : y + s • e + (-s) • e = y := by rw [neg_smul, add_neg_cancel_right]
    rw [hy] at this
    rw [abs_of_nonpos hs, abs_le]; constructor <;> linarith [this.1, this.2.1]

/-- The function `g = perturbG e α A` for open `A` satisfying the smallness hypothesis `hA`:
(a) `0 ≤ g ≤ ε`; (b) `g(x) ≤ g(x + s e) ≤ g(x) + s` for `s ≥ 0`, with equality if
`[x, x + s e] ⊆ A`; (c) `|g(x + v) - g(x)| ≤ |v| / tan α` for `v ∈ e^⊥`; hence
`|g(x + h) - g(x)| ≤ |h ⬝ e| + |h_W| / tan α` (`g` is continuous), and for `s > 0` the quotient
`(g(x + s e) - g(x)) / s` lies in `[0, 1]` and equals `1` if `[x, x + s e] ⊆ A`.
The hypothesis `hA` is the smallness condition `𝓛¹{u ∈ [a, b] : γ_η(u) ∈ A} ≤ ε` for all `t`-Lipschitz `η`. -/
theorem perturb_g (he : vecEuclideanNorm e = 1) (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (hε : 0 ≤ ε)
    (hA : ∀ a b η, IsConeGraphFn e α a b η → perturbMeas e A a b η ≤ ENNReal.ofReal ε) :
    (∀ x, 0 ≤ perturbG e α A x ∧ perturbG e α A x ≤ ε) ∧
    (∀ x, ∀ s : ℝ, 0 ≤ s →
      perturbG e α A x ≤ perturbG e α A (x + s • e) ∧
        perturbG e α A (x + s • e) ≤ perturbG e α A x + s ∧
        ((∀ σ ∈ Set.Icc 0 s, x + σ • e ∈ A) →
          perturbG e α A (x + s • e) = perturbG e α A x + s)) ∧
    (∀ x v, vecDot v e = 0 →
      |perturbG e α A (x + v) - perturbG e α A x| ≤ vecEuclideanNorm v / Real.tan α) ∧
    (∀ x h : Vec d, |perturbG e α A (x + h) - perturbG e α A x| ≤
      |vecDot h e| + vecEuclideanNorm (h - vecDot h e • e) / Real.tan α) ∧
    Continuous (perturbG e α A) ∧
    (∀ x, ∀ s : ℝ, 0 < s →
      0 ≤ (perturbG e α A (x + s • e) - perturbG e α A x) / s ∧
        (perturbG e α A (x + s • e) - perturbG e α A x) / s ≤ 1 ∧
        ((∀ σ ∈ Set.Icc 0 s, x + σ • e ∈ A) →
          (perturbG e α A (x + s • e) - perturbG e α A x) / s = 1)) := by
  have htpos : 0 < Real.tan α := Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2
  have hlip : ∀ x h : Vec d, |perturbG e α A (x + h) - perturbG e α A x| ≤
      |vecDot h e| + vecEuclideanNorm (h - vecDot h e • e) / Real.tan α := by
    intro x h
    have hsplit : x + h = (x + (h - vecDot h e • e)) + vecDot h e • e := by abel
    have h1 := perturbG_abs_smul he hα hα2 hε hA (x + (h - vecDot h e • e)) (vecDot h e)
    have h2 := perturbG_lipschitz_W he hα hα2 hε hA x (perturb_wPart_perp he h)
    rw [hsplit]
    calc _ = |(perturbG e α A (x + (h - vecDot h e • e) + vecDot h e • e) -
            perturbG e α A (x + (h - vecDot h e • e))) +
          (perturbG e α A (x + (h - vecDot h e • e)) - perturbG e α A x)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)
  refine ⟨fun x => perturbG_bounds he hα hα2 hε hA x, fun x s hs =>
    perturbG_monotone he hα hα2 hε hA x hs, fun x v hv =>
    perturbG_lipschitz_W he hα hα2 hε hA x hv, hlip, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    have hφ : Continuous fun h : Vec d =>
        |vecDot h e| + vecEuclideanNorm (h - vecDot h e • e) / Real.tan α := by
      have h1 := continuous_vecDot_left e (d := d)
      have h2 : Continuous fun h : Vec d => h - vecDot h e • e := by fun_prop
      exact (continuous_abs.comp h1).add ((continuous_vecEuclideanNorm.comp h2).div_const _)
    have h0 : Tendsto (fun y : Vec d => |vecDot (y - x) e| +
        vecEuclideanNorm ((y - x) - vecDot (y - x) e • e) / Real.tan α) (𝓝 x) (𝓝 0) := by
      have hc : Continuous fun y : Vec d => |vecDot (y - x) e| +
          vecEuclideanNorm ((y - x) - vecDot (y - x) e • e) / Real.tan α :=
        hφ.comp (continuous_id.sub continuous_const)
      have hn0 : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.mpr rfl
      simpa [vecDot_zero_left, hn0] using hc.tendsto x
    have : Tendsto (fun y : Vec d => perturbG e α A y - perturbG e α A x) (𝓝 x) (𝓝 0) := by
      refine squeeze_zero_norm (fun y => ?_) h0
      have := hlip x (y - x)
      rw [add_sub_cancel] at this
      simpa [Real.norm_eq_abs] using this
    have := this.add_const (perturbG e α A x)
    simpa [ContinuousAt] using this
  · intro x s hs
    have hm := perturbG_monotone he hα hα2 hε hA x hs.le
    refine ⟨div_nonneg (by linarith [hm.1]) hs.le, ?_, fun hseg => ?_⟩
    · rw [div_le_one hs]; linarith [hm.2.1]
    · rw [hm.2.2 hseg]; field_simp; ring

end AFree
