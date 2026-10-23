module

public import AFree.Curves.Rainwater.Defs

/-!
# Curve properties of `𝒢(C)`

Injective, `1`-Lipschitz, differentiable a.e. with `|γ'| ≤ 1` and `γ' ⬝ e ≥ cos α`; hence the
image of `γ ∈ 𝒢(C)` is a `C`-curve, contained in `B(k+1)` when `γ ∈ 𝒢_k`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The extension of `γ : [0,1] → ℝ^d` to `ℝ` by constants. -/
noncomputable def ccurveExt (γ : C(I, Vec d)) : ℝ → Vec d := Set.IccExtend zero_le_one γ

lemma ccurveExt_of_mem (γ : C(I, Vec d)) {s : ℝ} (hs : s ∈ I) :
    ccurveExt γ s = γ ⟨s, hs⟩ := Set.IccExtend_of_mem _ _ hs

lemma ccurveExt_coe (γ : C(I, Vec d)) (s : I) : ccurveExt γ s = γ s := Set.IccExtend_val _ _ _

lemma lipschitzWith_ccurveExt {e : Vec d} {α : ℝ} {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpace e α) :
    LipschitzWith 1 (ccurveExt γ) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 := ccurveSpace_dist_le hγ (Set.projIcc 0 1 zero_le_one y) (Set.projIcc 0 1 zero_le_one x)
  have h2 : |((Set.projIcc 0 1 zero_le_one x : I) : ℝ) - (Set.projIcc 0 1 zero_le_one y : I)| ≤
      |x - y| := Set.abs_projIcc_sub_projIcc zero_le_one
  have h3 := norm_le_vecEuclideanNorm (γ (Set.projIcc 0 1 zero_le_one x) -
    γ (Set.projIcc 0 1 zero_le_one y))
  simp only [ccurveExt, Set.IccExtend, Function.comp_apply, NNReal.coe_one, one_mul,
    dist_eq_norm, Real.norm_eq_abs]
  rw [abs_sub_comm] at h1
  rw [abs_sub_comm] at h2
  linarith

/-- Right difference quotients of the extension. -/
private lemma quotient_bounds {e : Vec d} {α : ℝ} {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpace e α)
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) {v : Vec d} (hv : HasDerivAt (ccurveExt γ) v s) :
    vecEuclideanNorm v ≤ 1 ∧ Real.cos α ≤ vecDot v e := by
  have hq := hv.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ s + t ≤ 1 := by
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 - s :=
      (eventually_lt_nhds (sub_pos.2 hs.2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
    exact ⟨ht0, by linarith⟩
  have key : ∀ t, 0 < t → s + t ≤ 1 →
      vecEuclideanNorm (t⁻¹ • (ccurveExt γ (s + t) - ccurveExt γ s)) ≤ 1 ∧
        Real.cos α ≤ vecDot (t⁻¹ • (ccurveExt γ (s + t) - ccurveExt γ s)) e := by
    intro t ht hst
    have hs1 : s + t ∈ I := ⟨by linarith [hs.1], hst⟩
    rw [ccurveExt_of_mem γ hs1, ccurveExt_of_mem γ ⟨hs.1, hs.2.le⟩]
    have hh := hγ ⟨s, hs.1, hs.2.le⟩ ⟨s + t, hs1⟩ (by change s ≤ s + t; linarith)
    simp only [add_sub_cancel_left] at hh
    constructor
    · rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 ht)]
      calc t⁻¹ * vecEuclideanNorm _ ≤ t⁻¹ * t := by gcongr; exact hh.1
        _ = 1 := inv_mul_cancel₀ ht.ne'
    · rw [Curves.vecDot_smul_left]
      calc Real.cos α = t⁻¹ * (Real.cos α * t) := by field_simp
        _ ≤ _ := by gcongr; exact hh.2
  constructor
  · refine le_of_tendsto ((PDE.continuous_vecEuclideanNorm.tendsto _).comp hq) ?_
    filter_upwards [hev] with t ht using (key t ht.1 ht.2).1
  · refine ge_of_tendsto ((Curves.continuous_vecDot_left e).tendsto _ |>.comp hq) ?_
    filter_upwards [hev] with t ht using (key t ht.1 ht.2).2

/-- For `γ ∈ 𝒢(C)`, `C = C(e, α)`: `γ` is injective and `1`-Lipschitz;
its (extended) derivative exists a.e. on `[0,1]` with `|γ'| ≤ 1`, `γ' ⬝ e ≥ cos α` (so `γ' ∈ C`
a.e.); `γ([0,1])` is a `C`-curve, contained in `B(k+1)` if `γ ∈ 𝒢_k`. -/
theorem ccurveSpace_curve_properties {e : Vec d} {α : ℝ}
    (hα : 0 < α) (hα2 : α < Real.pi / 2) {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpace e α) :
    Function.Injective γ ∧ LipschitzWith 1 γ ∧
    (∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)), DifferentiableAt ℝ (ccurveExt γ) s ∧
      vecEuclideanNorm (deriv (ccurveExt γ) s) ≤ 1 ∧
      Real.cos α ≤ vecDot (deriv (ccurveExt γ) s) e ∧ deriv (ccurveExt γ) s ∈ cone e α) ∧
    IsCCurve (cone e α) (range γ) ∧
    ∀ k : ℕ, γ ∈ ccurveSpaceK e α k → range γ ⊆ euclideanClosedBall 0 (k + 1) := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hc1 : Real.cos α ≤ 1 := Real.cos_le_one α
  have hext := lipschitzWith_ccurveExt hγ
  have hae : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)), DifferentiableAt ℝ (ccurveExt γ) s ∧
      vecEuclideanNorm (deriv (ccurveExt γ) s) ≤ 1 ∧
      Real.cos α ≤ vecDot (deriv (ccurveExt γ) s) e ∧ deriv (ccurveExt γ) s ∈ cone e α := by
    rw [← Measure.restrict_congr_set Ico_ae_eq_Icc]
    have hd := hext.ae_differentiableAt (μ := volume)
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ico] with s hs hsI
    obtain ⟨h1, h2⟩ := quotient_bounds hγ hsI hs.hasDerivAt
    refine ⟨hs, h1, h2, ?_⟩
    change Real.cos α * _ ≤ _
    nlinarith [vecEuclideanNorm_nonneg (deriv (ccurveExt γ) s)]
  refine ⟨?_, ?_, hae, ?_, ?_⟩
  · intro s s' h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hγ s s' hlt.le
      have h1 : γ s' - γ s = 0 := by rw [h, sub_self]
      rw [h1] at this
      simp only [Curves.vecDot_zero_left, vecEuclideanNorm] at this
      have h2 : (s : ℝ) < s' := hlt
      nlinarith [this.2]
    · have := hγ s' s hlt.le
      have h1 : γ s - γ s' = 0 := by rw [h, sub_self]
      rw [h1] at this
      simp only [Curves.vecDot_zero_left] at this
      have h2 : (s' : ℝ) < s := hlt
      nlinarith [this.2]
  · refine LipschitzWith.of_dist_le_mul fun s s' => ?_
    have h1 := ccurveSpace_dist_le hγ s s'
    have h3 := norm_le_vecEuclideanNorm (γ s' - γ s)
    simp only [dist_eq_norm, NNReal.coe_one, one_mul, Subtype.dist_eq, Real.norm_eq_abs]
    rw [norm_sub_rev, abs_sub_comm]
    linarith
  · refine ⟨0, 1, zero_le_one, ccurveExt γ, ⟨⟨1, hext⟩, ?_⟩, ?_⟩
    · filter_upwards [hae] with s hs using hs.2.2.2
    · ext x
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s, s.2, ccurveExt_coe γ s⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hs⟩, (ccurveExt_of_mem γ hs).symm⟩
  · intro k hk x ⟨s, hs⟩
    subst hs
    have := ccurveSpaceK_norm_le hk s
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le]
    · simpa using this
    · positivity

end AFree
