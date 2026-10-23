module

public import AFree.Curves.ConeCalc
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Increments characterize `C`-curves

A Lipschitz curve has derivative in `C` a.e. iff all its increments lie in `C`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- The linear functional `x ↦ x ⬝ w` on `Vec d`. -/
private noncomputable def dotCLM (w : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i, w i • ContinuousLinearMap.proj i

private lemma dotCLM_apply (w x : Vec d) : dotCLM w x = vecDot x w := by
  simp [dotCLM, vecDot, mul_comm]

private lemma ac_comp {γ : ℝ → Vec d} {a b : ℝ} {K : ℝ≥0} (hγ : LipschitzOnWith K γ (Icc a b))
    (L : Vec d →L[ℝ] ℝ) {p q : ℝ} (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) :
    AbsolutelyContinuousOnInterval (fun t => L (γ t)) p q := by
  have hl := L.lipschitzWith.comp_lipschitzOnWith hγ
  refine (hl.mono ?_).absolutelyContinuousOnInterval
  intro t ht
  rw [uIcc] at ht
  rcases le_total p q with h | h
  · rw [min_eq_left h, max_eq_right h] at ht
    exact ⟨hp.1.trans ht.1, ht.2.trans hq.2⟩
  · rw [min_eq_right h, max_eq_left h] at ht
    exact ⟨hq.1.trans ht.1, ht.2.trans hp.2⟩

private lemma ae_differentiableAt_Icc {γ : ℝ → Vec d} {a b : ℝ} {K : ℝ≥0}
    (hγ : LipschitzOnWith K γ (Icc a b)) (hab : a ≤ b) :
    ∀ᵐ t ∂(volume.restrict (Icc a b)), DifferentiableAt ℝ γ t := by
  have hai : ∀ i : Fin d, ∀ᵐ t, t ∈ uIcc a b → DifferentiableAt ℝ (fun t => γ t i) t := fun i =>
    (ac_comp hγ (ContinuousLinearMap.proj i) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)).ae_differentiableAt
  rw [← ae_all_iff] at hai
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hai] with t ht htm
  exact differentiableAt_pi.mpr fun i => ht i (by rwa [uIcc_of_le hab])

private lemma deriv_dot {γ : ℝ → Vec d} {t : ℝ} (hγ : DifferentiableAt ℝ γ t) (w : Vec d) :
    deriv (fun t => dotCLM w (γ t)) t = vecDot (deriv γ t) w := by
  have h : HasDerivAt (fun t => dotCLM w (γ t)) (dotCLM w (deriv γ t)) t :=
    (dotCLM w).hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
  rw [h.deriv, dotCLM_apply]

/-- For `γ` Lipschitz on `[a, b]` (`a ≤ b`) and `C = C(e, α)`,
`α ∈ (0, π/2)`: `γ' ∈ C` a.e. on `[a, b]` iff `γ(s') - γ(s) ∈ C` for all `a ≤ s ≤ s' ≤ b`. -/
theorem ccurve_incr_iff {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {γ : ℝ → Vec d} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b) (hγ : LipschitzOnWith K γ (Icc a b)) :
    (∀ᵐ s ∂(volume.restrict (Icc a b)), deriv γ s ∈ cone e α) ↔
      ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s ≤ s' → γ s' - γ s ∈ cone e α := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hdiff := ae_differentiableAt_Icc hγ hab
  constructor
  · intro hcone s hs s' hs' hss'
    set Δ := γ s' - γ s with hΔ
    -- the two scalar functions
    have hacw : AbsolutelyContinuousOnInterval (fun t => dotCLM Δ (γ t)) s s' :=
      ac_comp hγ _ hs hs'
    have hace : AbsolutelyContinuousOnInterval (fun t => dotCLM e (γ t)) s s' :=
      ac_comp hγ _ hs hs'
    have hIw := hacw.integral_deriv_eq_sub
    have hIe := hace.integral_deriv_eq_sub
    have hiw := hacw.intervalIntegrable_deriv
    have hie := hace.intervalIntegrable_deriv
    have hineq : ∀ᵐ t ∂(volume.restrict (Icc s s')),
        deriv (fun t => dotCLM Δ (γ t)) t ≤
          vecEuclideanNorm Δ / Real.cos α * deriv (fun t => dotCLM e (γ t)) t := by
      have hsub : volume.restrict (Icc s s') ≤ volume.restrict (Icc a b) :=
        Measure.restrict_mono (Icc_subset_Icc hs.1 hs'.2) le_rfl
      have h1 := ae_mono hsub hcone
      have h2 := ae_mono hsub hdiff
      filter_upwards [h1, h2] with t ht1 ht2
      rw [deriv_dot ht2, deriv_dot ht2]
      have hn := norm_le_of_mem_cone hα hα2 ht1
      have hcs := (le_abs_self _).trans (abs_vecDot_le_vecEuclideanNorm_mul (deriv γ t) Δ)
      calc vecDot (deriv γ t) Δ ≤ vecEuclideanNorm (deriv γ t) * vecEuclideanNorm Δ := hcs
        _ ≤ (vecDot (deriv γ t) e / Real.cos α) * vecEuclideanNorm Δ :=
            mul_le_mul_of_nonneg_right hn (vecEuclideanNorm_nonneg _)
        _ = _ := by ring
    have hmono := intervalIntegral.integral_mono_ae_restrict hss' hiw (hie.const_mul _) hineq
    rw [intervalIntegral.integral_const_mul, hIw, hIe] at hmono
    simp only [dotCLM_apply] at hmono
    have hsq : vecDot (γ s' - γ s) (γ s' - γ s) = vecEuclideanNorm Δ ^ 2 := by
      rw [vecDot_self, vecEuclideanNorm_sq]
    have hsub : vecDot (γ s') (γ s' - γ s) - vecDot (γ s) (γ s' - γ s) =
        vecEuclideanNorm Δ ^ 2 := by rw [← vecDot_sub_left, hsq]
    have hsub2 : vecDot (γ s') e - vecDot (γ s) e = vecDot Δ e := by
      rw [hΔ, vecDot_sub_left]
    rw [hsub, hsub2] at hmono
    show Real.cos α * vecEuclideanNorm Δ ≤ vecDot Δ e
    rcases eq_or_lt_of_le (vecEuclideanNorm_nonneg Δ) with h0 | hpos
    · rw [← h0]; have : vecDot Δ e = 0 := by
        rw [vecEuclideanNorm_eq_zero_iff.mp h0.symm]; exact vecDot_zero_left e
      simp [this]
    · rw [div_mul_eq_mul_div, le_div_iff₀ hc] at hmono
      nlinarith
  · intro hinc
    have hlt : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∈ Ioo a b := by
      rw [ae_restrict_iff' measurableSet_Icc]
      have hne : ∀ x : ℝ, ∀ᵐ t : ℝ, t ≠ x := fun x => by
        rw [ae_iff]; simp
      have : ∀ᵐ t : ℝ, t ≠ a ∧ t ≠ b := (hne a).and (hne b)
      filter_upwards [this] with t ht htm
      exact ⟨lt_of_le_of_ne htm.1 (Ne.symm ht.1), lt_of_le_of_ne htm.2 ht.2⟩
    filter_upwards [hdiff, hlt] with t ht htI
    have hslope := ht.hasDerivAt.tendsto_slope_zero_right
    refine (cone_isClosed e α).mem_of_tendsto hslope ?_
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 (b - t) := Ioo_mem_nhdsGT (by linarith [htI.2])
    filter_upwards [hev] with h hh
    exact cone_smul_mem (hinc t ⟨htI.1.le, htI.2.le⟩ (t + h) ⟨by linarith [htI.1, hh.1],
      by linarith [hh.2]⟩ (by linarith [hh.1])) (inv_nonneg.mpr hh.1.le)
end AFree
