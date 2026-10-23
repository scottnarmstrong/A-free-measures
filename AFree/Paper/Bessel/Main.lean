module

public import AFree.Paper.Bessel.Kernel
public import AFree.Paper.Bessel.CCompact

/-!
# Lemma 2.1: compactness of the Bessel potential

[DPR, Lemma 2.1]. For `d ≥ 1`, `T f = (Re b) ⋆ f` with `b` the Bessel kernel; it is compact as a norm
limit of the compact operators `S_β`, `β ∈ C_c`. For `d = 0` the space is a point and `T` is rank one.
-/

@[expose] public section

open MeasureTheory PDE
open scoped ENNReal

namespace AFree.Bessel

variable {d : ℕ}

theorem exists_compact_pos (hd : 0 < d) {s : ℝ} (hs : 0 < s) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p < besselExponent d s) :
    ∃ T : L1Ball d →L[ℝ] Lp ℝ p (volume : Measure (Vec d)), IsCompactOperator T ∧
      ∀ u : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → tsupport u ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ f : L1Ball d, ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume] u →
          ((T f : Lp ℝ p (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume]
            fun x => (besselPotential s u x).re := by
  have hpt : p ≠ ⊤ := ne_top_of_lt (hp.trans_le le_top)
  obtain ⟨_, hbp, _⟩ := besselKernel_c hd hs Fact.out hp
  refine ⟨convBall hpt hbp, ?_, ?_⟩
  · have hcl := isClosed_setOfPred_isCompactOperator (σ₁₂ := RingHom.id ℝ) (M₁ := L1Ball d)
      (M₂ := Lp ℝ p (volume : Measure (Vec d)))
    suffices hmem : convBall hpt hbp ∈ closure {T : L1Ball d →L[ℝ] Lp ℝ p (volume : Measure (Vec d)) | IsCompactOperator T} by
      rw [hcl.closure_eq] at hmem; exact hmem
    refine (Metric.mem_closure_iff (α := L1Ball d →L[ℝ] Lp ℝ p (volume : Measure (Vec d)))).2 fun ε hε => ?_
    obtain ⟨β, hβs, hβn, hβc, hβm⟩ := (hbp.exists_hasCompactSupport_eLpNorm_sub_le hpt
      (ε := ENNReal.ofReal (ε / 2)) (by simpa using half_pos hε))
    refine ⟨convBall hpt hβm, isCompactOperator_convBall hpt hβc hβs, ?_⟩
    have h1 : convBall hpt hbp - convBall hpt hβm = (convLp hpt (hbp.sub hβm)).comp
        (L1Ball d).subtypeL := by
      rw [convLp_sub hpt hbp hβm]; rfl
    refine lt_of_eq_of_lt (dist_eq_norm (E := L1Ball d →L[ℝ] Lp ℝ p (volume : Measure (Vec d))) _ _) ?_
    rw [h1]
    have h2 : ‖(convLp hpt (hbp.sub hβm)).comp (L1Ball d).subtypeL‖ ≤ ε / 2 := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le _) (norm_nonneg _)).trans ?_
      rw [mul_one]
      refine (norm_convLp_le hpt _).trans ?_
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hβn
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  · intro u hu hsupp f hf
    have hc : HasCompactSupport u :=
      IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec d) 1) (isClosed_tsupport u)
        (fun y hy => Metric.ball_subset_closedBall
          (euclideanBall_subset_supBall (x₀ := (0 : Vec d)) (R := 1) one_pos (hsupp hy)))
    obtain ⟨M, hM⟩ := hu.continuous.bounded_above_of_compact_support hc
    filter_upwards [coeFn_convLp hpt hbp (f : Lp ℝ 1 (volume : Measure (Vec d)))] with x hx
    rw [convBall_apply, hx, convFn_congr_right hf x]
    have hint : Integrable fun y => besselKernel d s (x - y) * (u y : ℂ) :=
      ((besselKernel_a (d := d) hs).1.comp_sub_left x).mul_bdd (c := M) (Complex.continuous_ofReal.comp
        hu.continuous).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by simpa using hM y)
    rw [besselKernel_d hs u hu hsupp x]
    unfold convFn
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [Complex.mul_re]


/-- In dimension zero, `volume` is a Dirac mass, hence a probability measure. -/
theorem volume_zero : (volume : Measure (Vec 0)) = Measure.dirac default := by
  show Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) = _
  rw [Measure.pi_of_empty]
  congr 1; exact Subsingleton.elim _ _

theorem exists_compact_zero {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    ∃ T : L1Ball 0 →L[ℝ] Lp ℝ p (volume : Measure (Vec 0)), IsCompactOperator T ∧
      ∀ u : Vec 0 → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → tsupport u ⊆ euclideanBall (0 : Vec 0) 1 →
        ∀ f : L1Ball 0, ((f : Lp ℝ 1 (volume : Measure (Vec 0))) : Vec 0 → ℝ) =ᵐ[volume] u →
          ((T f : Lp ℝ p (volume : Measure (Vec 0))) : Vec 0 → ℝ) =ᵐ[volume]
            fun x => (besselPotential s u x).re := by
  have : IsProbabilityMeasure (volume : Measure (Vec 0)) :=
    ⟨by rw [volume_zero]; simp⟩
  let e : Lp ℝ p (volume : Measure (Vec 0)) := (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))
  let ev : L1Ball 0 →L[ℝ] ℝ := (L1.integralCLM (E := ℝ) (μ := (volume : Measure (Vec 0)))).comp
    (L1Ball 0).subtypeL
  have hev : ∀ f : L1Ball 0, ev f = ∫ x, ((f : Lp ℝ 1 (volume : Measure (Vec 0))) : Vec 0 → ℝ) x :=
    fun f => by rw [← L1.integral_eq_integral, L1.integral_eq]; rfl
  refine ⟨ev.smulRight e, ?_, ?_⟩
  · refine (isCompactOperator_iff_image_closedBall_subset_compact
      (ev.smulRight e : L1Ball 0 →ₗ[ℝ] Lp ℝ p (volume : Measure (Vec 0))) one_pos).2
      ⟨(fun c : ℝ => c • e) '' Set.Icc (-‖ev‖) ‖ev‖,
        (isCompact_Icc).image (continuous_id.smul continuous_const), ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨ev f, ?_, rfl⟩
    have h1 : ‖f‖ ≤ 1 := by simpa using hf
    have h2 : ‖ev f‖ ≤ ‖ev‖ := (ev.le_opNorm f).trans (mul_le_of_le_one_right (norm_nonneg _) h1)
    exact abs_le.1 h2
  · intro u hu hsupp f hf
    have hsub : ∀ (g : Vec 0 → ℝ) (x : Vec 0), g x = g default := fun g x => by
      rw [Subsingleton.elim x default]
    have hu0 : ∀ x, ∫ y, u y = u x := fun x => by
      rw [volume_zero, integral_dirac, hsub u x]
    have hbp : ∀ x, (besselPotential s u x).re = u x := fun x => by
      simp only [besselPotential, vecFourierTransform, volume_zero, integral_dirac]
      simp [vecDot, vecNormSq, hsub u x]
    filter_upwards [Lp.coeFn_smul (ev ↑f) e, MemLp.coeFn_toLp (memLp_const (1 : ℝ))] with x h1 h2
    show ((ev f • e : Lp ℝ p (volume : Measure (Vec 0))) : Vec 0 → ℝ) x = _
    rw [h1, Pi.smul_apply, show (e : Vec 0 → ℝ) x = 1 from h2, smul_eq_mul, mul_one, hev,
      integral_congr_ae hf, hu0 x, hbp x]


/-- [DPR, Lemma 2.1]: for `s > 0` and `1 ≤ p < p(d,s)` there is a compact operator
`T : L¹_c(B₁) → L^p` with `T u = Re (Id - Δ)^{-s/2} u` a.e. for smooth `u` supported in `B₁`. -/
theorem bessel_compact {s : ℝ} (hs : 0 < s) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p < besselExponent d s) :
    ∃ T : L1Ball d →L[ℝ] Lp ℝ p (volume : Measure (Vec d)), IsCompactOperator T ∧
      ∀ u : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → tsupport u ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ f : L1Ball d, ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume] u →
          ((T f : Lp ℝ p (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume]
            fun x => (besselPotential s u x).re := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact exists_compact_zero
  · exact exists_compact_pos hd hs hp

end AFree.Bessel
