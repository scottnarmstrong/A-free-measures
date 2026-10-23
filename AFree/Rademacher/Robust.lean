module

public import AFree.Rademacher.Directional
public import AFree.Rademacher.Setting
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Robustness of the lower bound for `U_σ`

The lower bound for `U_σ` survives small uniform perturbations; this replaces the continuity-point lemma [AM, Lemma 4.12] in the explicit iteration.
-/

@[expose] public section

open PDE Filter Topology Set MeasureTheory
open scoped NNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- Mean value theorem for the difference quotient of a differentiable function along `v`. -/
theorem exists_dirQuot_eq {F : Vec d → ℝ} (hF : Differentiable ℝ F) (v x : Vec d) {h : ℝ}
    (hh : 0 < h) : ∃ c ∈ Ioo 0 h, dirQuot F v x h = fderiv ℝ F (x + c • v) v := by
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F (x + t • v)) (fderiv ℝ F (x + t • v) v) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact (hF _).hasFDerivAt.comp_hasDerivAt t h1
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => F (x + t • v))
    (fun t => fderiv ℝ F (x + t • v) v) hh
    (fun t _ => (hder t).continuousAt.continuousWithinAt) fun t _ => hder t
  refine ⟨c, hc, ?_⟩
  rw [hceq]
  simp [dirQuot]

/-- Robustness of the lower bound for `U_σ`. In the setting `(S)`, let `F ∈ X₀`,
`K` compact and `σ > 0` with `U_σ F ≥ D` on `K` (where `v = ε_i`, `D = δ / (3 √m)`). Then there
is `σ' ∈ (0, σ)` such that every Lipschitz `g` with `‖g - F‖_sup ≤ η := D σ' / 32` satisfies
`U_σ g ≥ D / 2` on `K`. -/
theorem lem_robust {μ : Measure (Vec d)} {V : Vec d → Submodule ℝ (Vec d)} {i : Fin d} {m : ℕ}
    {δ : ℝ} {E : Set (Vec d)} {e : Vec d → Fin d → Vec d}
    (hS : Setting μ V i m δ E e) {F : Vec d → ℝ} (hF : F ∈ X0 e) {K : Set (Vec d)}
    (hK : IsCompact K) {σ : ℝ} (hσ : 0 < σ)
    (hU : ∀ x ∈ K, settingD δ m ≤ dirOsc F (basisVec i) σ 0 x) :
    ∃ σ' : ℝ, 0 < σ' ∧ σ' < σ ∧ ∀ g : Vec d → ℝ, IsLipFun g →
      (∀ y, |g y - F y| ≤ settingD δ m * σ' / 32) →
      ∀ x ∈ K, settingD δ m / 2 ≤ dirOsc g (basisVec i) σ 0 x := by
  set D := settingD δ m with hD
  have hDpos : 0 < D := hS.settingD_pos
  set v : Vec d := basisVec i with hvdef
  have hv : vecEuclideanNorm v = 1 := vecEuclideanNorm_basisVec i
  have hFd : Differentiable ℝ F := hF.1.differentiable (by simp)
  have hFlip : IsLipFun F := ⟨_, (X0_lipschitz hS.frame).2.1 F hF⟩
  have hφ : Continuous fun z => fderiv ℝ F z v :=
    (hF.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hK' : IsCompact (Metric.cthickening σ K) := hK.cthickening
  obtain ⟨θ, hθ, hθ'⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hφ.continuousOn) (D / 16) (by positivity)
  set σ' := min (θ / 3) (σ / 2) with hσ'
  have hσ'pos : 0 < σ' := lt_min (by positivity) (by positivity)
  have hσ'σ : σ' < σ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hσ'θ : σ' ≤ θ / 3 := min_le_left _ _
  have hσ'half : σ' ≤ σ / 2 := min_le_right _ _
  -- the point `x + c v` for `0 < c < σ` lies in the thickening
  have hmem : ∀ x ∈ K, ∀ c : ℝ, 0 < c → c < σ → x + c • v ∈ Metric.cthickening σ K := by
    intro x hx c hc hcσ
    refine Metric.mem_cthickening_of_dist_le _ x σ K hx ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have := norm_le_vecEuclideanNorm v
    nlinarith
  -- oscillation of the difference quotient at scale `σ'`
  have hclose : ∀ x ∈ K, ∀ h ∈ Ioc 0 σ',
      |dirQuot F v x h - dirQuot F v x (2 * σ')| < D / 16 := by
    intro x hx h hh
    obtain ⟨c, hc, hceq⟩ := exists_dirQuot_eq hFd v x hh.1
    obtain ⟨c₀, hc₀, hceq₀⟩ := exists_dirQuot_eq hFd v x (show 0 < 2 * σ' by positivity)
    rw [hceq, hceq₀]
    have hdist : dist (x + c • v) (x + c₀ • v) < θ := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
      have h1 := norm_le_vecEuclideanNorm v
      rw [hv] at h1
      have h2 : |c - c₀| < 2 * σ' := by
        rw [abs_lt]; constructor <;> linarith [hc.1, hc.2, hc₀.1, hc₀.2, hh.2]
      calc |c - c₀| * ‖v‖ ≤ |c - c₀| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ < θ := by linarith
    have := hθ' _ (hmem x hx c hc.1 (by linarith [hc.2, hh.2])) _
      (hmem x hx c₀ hc₀.1 (by linarith [hc₀.2])) hdist
    simpa [Real.dist_eq] using this
  have hne : ∀ s t : ℝ, s < t → (Ioc s t).Nonempty := fun s t hst => ⟨t, hst, le_rfl⟩
  have hbdd : ∀ x : Vec d, BddAbove (dirQuot F v x '' Ioc σ' σ) ∧
      BddBelow (dirQuot F v x '' Ioc σ' σ) := by
    obtain ⟨Kc, hKc⟩ := hFlip
    intro x
    refine ⟨⟨Kc, ?_⟩, ⟨-Kc, ?_⟩⟩ <;> rintro _ ⟨h, hh, rfl⟩ <;>
      have := abs_dirQuot_le hKc hv x (ne_of_gt (hσ'pos.trans hh.1)) <;> [exact (abs_le.1 this).2;
        exact (abs_le.1 this).1]
  refine ⟨σ', hσ'pos, hσ'σ, fun g hg hgF x hx => ?_⟩
  -- `U_{σ,σ'} F ≥ U_σ F - D/4`
  have hsup : dirSup F v σ 0 x ≤ dirSup F v σ σ' x + D / 8 := by
    refine csSup_le ((hne 0 σ hσ).image _) ?_
    rintro _ ⟨h, hh, rfl⟩
    by_cases hle : h ≤ σ'
    · have h1 := hclose x hx h ⟨hh.1, hle⟩
      have h2 : dirQuot F v x (2 * σ') ≤ dirSup F v σ σ' x :=
        le_csSup (hbdd x).1 ⟨2 * σ', ⟨by linarith, by linarith⟩, rfl⟩
      linarith [(abs_lt.1 h1).2]
    · have : dirQuot F v x h ≤ dirSup F v σ σ' x :=
        le_csSup (hbdd x).1 ⟨h, ⟨not_le.1 hle, hh.2⟩, rfl⟩
      linarith
  have hinf : dirInf F v σ σ' x - D / 8 ≤ dirInf F v σ 0 x := by
    refine le_csInf ((hne 0 σ hσ).image _) ?_
    rintro _ ⟨h, hh, rfl⟩
    by_cases hle : h ≤ σ'
    · have h1 := hclose x hx h ⟨hh.1, hle⟩
      have h2 : dirInf F v σ σ' x ≤ dirQuot F v x (2 * σ') :=
        csInf_le (hbdd x).2 ⟨2 * σ', ⟨by linarith, by linarith⟩, rfl⟩
      linarith [(abs_lt.1 h1).1]
    · have : dirInf F v σ σ' x ≤ dirQuot F v x h :=
        csInf_le (hbdd x).2 ⟨h, ⟨not_le.1 hle, hh.2⟩, rfl⟩
      linarith
  have hUx := hU x hx
  have hFσ' : 3 * D / 4 ≤ dirOsc F v σ σ' x := by
    unfold dirOsc at hUx ⊢
    linarith
  have hdep := (dirOsc_lipschitz_dependence hFlip hg hv (σ := σ) hσ'pos hgF x).2.2
  have hM : 4 * (D * σ' / 32) / σ' = D / 8 := by field_simp; ring
  rw [hM] at hdep
  have hmono := dirOsc_le_dirOsc_zero hg hv (σ := σ) hσ'pos.le x
  linarith [(abs_le.1 hdep).1]

end AFree.Rademacher
