module

public import AFree.Harmonic.WeakTypeKernel.Finite

/-!
# The weak-type estimate given Calderón–Zygmund stopping cubes

For a smooth compactly supported field `F` vanishing off the root box `I` and stopping cubes `S`
at height `ℓ`, the set `{|K ⋆ F_i| > λ}` has measure at most
`4·2^d A² ℓ ‖F‖₁ / λ² + 2^d C_d ‖F‖₁ / ℓ + 4 C(d) A ‖F‖₁ / λ`.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter PDE PDE.NewtonWeakType
open scoped ENNReal Topology

namespace AFree

noncomputable section

variable {d : ℕ} {I : Box (Fin d)} {F : Vec d → Vec d} {ℓ : ℝ} {K : Vec d → ℝ} {A : ℝ}

/-- Mollifying a smooth compactly supported field recovers the convolution in the limit. -/
theorem tendsto_abs_kconv_mollVec (hK : HormanderKernel K A) {F : Vec d → Vec d}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (i : Fin d) (x : Vec d) :
    Tendsto (fun a => |kconv K i (mollVec a F) x|) (𝓝[>] (0 : ℝ)) (𝓝 |kconv K i F x|) := by
  have hv := vbdd_of_smooth hF hFc
  have hFi : ContDiff ℝ (⊤ : ℕ∞) fun z => F z i := contDiff_pi.mp hF i
  have hFci : HasCompactSupport fun z => F z i := hasCompactSupport_apply hFc i
  set N : ℝ := ∫ y, |K y| with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => abs_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (2 * (N + 1)) := by positivity
  obtain ⟨a₀, ha₀, hclose⟩ := exists_forall_dist_wholeSpaceMollify_le hFi.continuous hFci hδ
  filter_upwards [Ioc_mem_nhdsGT ha₀] with a ha
  have hdiff : kconv K i (mollVec a F) x - kconv K i F x =
      ∫ y, K (x - y) * (mollVec a F y i - F y i) := by
    unfold kconv
    simp_rw [mul_sub]
    rw [integral_sub (integrable_kconv_term hK.integrable ha.1 hv i x)
      (integrable_kernel_mul hK.integrable hFi.continuous hFci x)]
  have hbd : |kconv K i (mollVec a F) x - kconv K i F x| ≤ ε / (2 * (N + 1)) * N := by
    rw [hdiff]
    exact abs_integral_kernel_mul_le hK.integrable (fun y => by
      have := hclose a ha.1 ha.2 y
      rw [Real.dist_eq] at this
      exact this) x
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _) (lt_of_le_of_lt hbd ?_)
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- **The weak-type estimate given stopping cubes.** -/
theorem volume_kconv_gt_le_of_stopping (hK : HormanderKernel K A) (hd : 0 < d) (i : Fin d)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hFsupp : ∀ x, x ∉ (I : Set (Vec d)) → F x = 0) (S : CZStopping I F ℓ)
    {lam : ℝ} (hlam : 0 < lam) :
    volume {x | lam < |kconv K i F x|} ≤
      ENNReal.ofReal (4 * 2 ^ d * A ^ 2 * ℓ * (∫ x, vecEuclideanNorm (F x)) / lam ^ 2 +
        2 ^ d * (czDilateConst d).toReal * (∫ x, vecEuclideanNorm (F x)) / ℓ +
        4 * (hormanderConst d * (2 ^ (d + 1) * A)) * (∫ x, vecEuclideanNorm (F x)) / lam) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hℓ := S.lam_pos
  have hA := hK.nonneg
  have hv := vbdd_of_smooth hF hFc
  have hFi : ∀ i, Continuous fun x => F x i := fun i => (contDiff_pi.mp hF i).continuous
  have hFI : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)) := fun i =>
    ((hFi i).integrable_of_hasCompactSupport (hasCompactSupport_apply hFc i)).integrableOn
  obtain ⟨M2, hM2⟩ := exists_vecNormSq_le hv
  have hM20 : 0 ≤ M2 := (vecNormSq_nonneg (F 0)).trans (hM2 0)
  set m : ℝ := ∫ x, vecEuclideanNorm (F x) with hm
  have hm0 : 0 ≤ m := integral_nonneg fun _ => vecEuclideanNorm_nonneg _
  have hL := lintegral_root_eq (I := I) hF hFc hFsupp
  rw [← hm] at hL
  have htot : ∑' k, volume (S.cube k : Set (Vec d)) ≠ ⊤ := by
    intro htop
    have h := S.tsum_volume_le
    rw [htop, hL, ENNReal.mul_top (by simpa using hℓ)] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero htot
  have hCd : czDilateConst d = ENNReal.ofReal (czDilateConst d).toReal :=
    (ENNReal.ofReal_toReal (czDilateConst_ne_top d)).symm
  set H : ℝ := hormanderConst d * (2 ^ (d + 1) * A) with hH
  have hH0 : 0 ≤ H := mul_nonneg (hormanderConst_nonneg d) (by positivity)
  set Cd : ℝ := (czDilateConst d).toReal with hCdd
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set Kc : ℝ := (lam / 2)⁻¹ ^ 2 * (A ^ 2 + 1) * (M2 + 1) with hKc
  have hKc0 : 0 < Kc := by positivity
  have hδ : 0 < (ε : ℝ) / Kc := by positivity
  obtain ⟨s, hs⟩ := (htail.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))).exists
  have htailfin : (∑' k : {k // k ∉ s}, volume (S.cube k : Set (Vec d))) ≠ ⊤ :=
    ne_top_of_lt hs
  have htailr : (∑' k : {k // k ∉ s}, volume (S.cube k : Set (Vec d))).toReal < (ε : ℝ) / Kc :=
    (ENNReal.toReal_lt_of_lt_ofReal hs)
  have hlint := lintegral_vecNormSq_czTrunc_le (S := S) hF.continuous.measurable hFI hFsupp hM2 s
  rw [hL] at hlint
  set tl : ℝ≥0∞ := ∑' k : {k // k ∉ s}, volume (S.cube k : Set (Vec d)) with htl
  have hUne : ENNReal.ofReal (2 ^ d * ℓ) * ENNReal.ofReal m + ENNReal.ofReal M2 * tl ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top htailfin⟩
  have hmeasq : AEStronglyMeasurable (fun x => vecNormSq (czTrunc S s x)) volume := by
    simp_rw [vecNormSq_eq_sum_sq]
    exact (Finset.measurable_sum _ fun i _ =>
      ((vbdd_czTrunc S hv s i).meas).pow_const 2).aestronglyMeasurable
  have hint : ∫ x, vecNormSq (czTrunc S s x) ≤ 2 ^ d * ℓ * m + M2 * tl.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
      hmeasq]
    refine (ENNReal.toReal_mono hUne hlint).trans (le_of_eq ?_)
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htailfin), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hm0,
      ENNReal.toReal_ofReal hM20]
  have hsa : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ k ∈ s, Real.sqrt d * a ≤ czRadius S k :=
    (Filter.eventually_all_finset s).mpr fun k _ => eventually_sqrt_mul_le d (czRadius_pos S hd k)
  have hbd : ∀ᶠ a in 𝓝[>] (0 : ℝ), volume {x | lam < |kconv K i (mollVec a F) x|} ≤
      ENNReal.ofReal ((lam / 2)⁻¹ ^ 2 * (A ^ 2 * ∫ x, vecNormSq (czTrunc S s x))) +
        (volume (czExceptional S) +
          ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal H * (2 * ENNReal.ofReal m))) := by
    filter_upwards [self_mem_nhdsWithin, hsa] with a ha hsa'
    have := volume_kconv_mollVec_gt_le S hK hv hFI s ha hsa' i hlam
    rwa [hL] at this
  have hlim := volume_gt_le_of_tendsto (Φ := fun a x => |kconv K i (mollVec a F) x|)
    (Φ₀ := fun x => |kconv K i F x|)
    (fun x => tendsto_abs_kconv_mollVec hK hF hFc i x) hbd
  refine hlim.trans ?_
  have hE := volume_czExceptional_le (S := S) hd
  rw [hL, hCd] at hE
  have h1 : (lam / 2)⁻¹ ^ 2 * (A ^ 2 * ∫ x, vecNormSq (czTrunc S s x)) ≤
      4 * 2 ^ d * A ^ 2 * ℓ * m / lam ^ 2 + ε := by
    have hc : 0 ≤ (lam / 2)⁻¹ ^ 2 * A ^ 2 := by positivity
    have hM : M2 * tl.toReal ≤ (M2 + 1) * ((ε : ℝ) / Kc) :=
      mul_le_mul (by linarith) htailr.le ENNReal.toReal_nonneg (by linarith)
    have hlast : (lam / 2)⁻¹ ^ 2 * A ^ 2 * ((M2 + 1) * ((ε : ℝ) / Kc)) ≤ ε := by
      have : (lam / 2)⁻¹ ^ 2 * (A ^ 2 + 1) * ((M2 + 1) * ((ε : ℝ) / Kc)) = ε := by
        rw [hKc]; field_simp
      have h2 : (lam / 2)⁻¹ ^ 2 * A ^ 2 * ((M2 + 1) * ((ε : ℝ) / Kc)) ≤
          (lam / 2)⁻¹ ^ 2 * (A ^ 2 + 1) * ((M2 + 1) * ((ε : ℝ) / Kc)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : 0 ≤ (lam / 2)⁻¹ ^ 2 := by positivity
        nlinarith
      linarith
    calc (lam / 2)⁻¹ ^ 2 * (A ^ 2 * ∫ x, vecNormSq (czTrunc S s x))
        ≤ (lam / 2)⁻¹ ^ 2 * (A ^ 2 * (2 ^ d * ℓ * m + M2 * tl.toReal)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hint (sq_nonneg _)) (by positivity)
      _ = (lam / 2)⁻¹ ^ 2 * A ^ 2 * (2 ^ d * ℓ * m) +
            (lam / 2)⁻¹ ^ 2 * A ^ 2 * (M2 * tl.toReal) := by ring
      _ ≤ (lam / 2)⁻¹ ^ 2 * A ^ 2 * (2 ^ d * ℓ * m) +
            (lam / 2)⁻¹ ^ 2 * A ^ 2 * ((M2 + 1) * ((ε : ℝ) / Kc)) := by
          gcongr
      _ ≤ 4 * 2 ^ d * A ^ 2 * ℓ * m / lam ^ 2 + ε := by
          have : (lam / 2)⁻¹ ^ 2 * A ^ 2 * (2 ^ d * ℓ * m) =
              4 * 2 ^ d * A ^ 2 * ℓ * m / lam ^ 2 := by
            field_simp
            ring
          linarith
  have h2 : volume (czExceptional S) ≤ ENNReal.ofReal (2 ^ d * Cd * m / ℓ) := by
    refine hE.trans (le_of_eq ?_)
    have hCd0 : 0 ≤ Cd := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_mul hCd0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have h3 : ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal H * (2 * ENNReal.ofReal m)) =
      ENNReal.ofReal (4 * H * m / lam) := by
    have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [this, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hH0,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  have hQ : 0 ≤ 4 * 2 ^ d * A ^ 2 * ℓ * m / lam ^ 2 := by positivity
  calc ENNReal.ofReal ((lam / 2)⁻¹ ^ 2 * (A ^ 2 * ∫ x, vecNormSq (czTrunc S s x))) +
        (volume (czExceptional S) +
          ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal H * (2 * ENNReal.ofReal m)))
      ≤ ENNReal.ofReal (4 * 2 ^ d * A ^ 2 * ℓ * m / lam ^ 2 + ε) +
        (ENNReal.ofReal (2 ^ d * Cd * m / ℓ) + ENNReal.ofReal (4 * H * m / lam)) := by
        rw [h3]
        exact add_le_add (ENNReal.ofReal_le_ofReal h1) (add_le_add h2 le_rfl)
    _ = ENNReal.ofReal (4 * 2 ^ d * A ^ 2 * ℓ * m / lam ^ 2 + ε +
          (2 ^ d * Cd * m / ℓ + 4 * H * m / lam)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal ((4 * 2 ^ d * A ^ 2 * ℓ * m / lam ^ 2 + 2 ^ d * Cd * m / ℓ +
          4 * H * m / lam) + ε) := by
        congr 1; ring
    _ ≤ ENNReal.ofReal (4 * 2 ^ d * A ^ 2 * ℓ * m / lam ^ 2 + 2 ^ d * Cd * m / ℓ +
          4 * H * m / lam) + ε := by
        refine (ENNReal.ofReal_add_le).trans ?_
        rw [ENNReal.ofReal_coe_nnreal]

end

end AFree
