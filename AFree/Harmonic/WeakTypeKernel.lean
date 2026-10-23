module

public import AFree.Harmonic.WeakTypeKernel.Stopping

/-!
# Weak type (1,1) for convolution with a Hörmander kernel

A smooth integrable kernel `K` with an `L²` bound of constant `A` on smooth compactly supported
functions and the gradient condition `|∇K(x) v| ≤ A |v| / |x|^{d+1}` gives the local weak-type
(1,1) estimate with constant `C(d) A`.  The proof is the Calderón–Zygmund argument, as for the Newtonian potential, with the kernel left abstract.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter PDE PDE.NewtonWeakType
open scoped ENNReal Topology

namespace AFree

noncomputable section

variable {d : ℕ}

theorem vecEuclideanNorm_single (i : Fin d) (r : ℝ) : vecEuclideanNorm (Pi.single i r : Vec d) = |r| := by
  unfold vecEuclideanNorm
  rw [vecNormSq_eq_sum_sq]
  simp [Pi.single_apply, Real.sqrt_sq_eq_abs]

/-- Weak type (1,1), local form, for a smooth integrable kernel with an L² bound and the Hörmander
gradient condition; the constant is `C(d) * A`. -/
theorem exists_weakTypeOne_of_hormander {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Vec d → ℝ) (A : ℝ), ContDiff ℝ (⊤ : ℕ∞) K → Integrable K → 0 ≤ A →
      (∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ∫ x, (∫ y, K (x - y) * f y) ^ 2 ≤ A ^ 2 * ∫ x, f x ^ 2) →
      (∀ x : Vec d, x ≠ 0 → ∀ v : Vec d,
        |fderiv ℝ K x v| ≤ A * vecEuclideanNorm v / vecEuclideanNorm x ^ (d + 1)) →
      ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → tsupport f ⊆ euclideanBall (0 : Vec d) 1 →
      ∀ lam : ℝ, 0 < lam →
        volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < |∫ y, K (x - y) * f y|} ≤
          ENNReal.ofReal (C * A / lam * ∫ x, |f x|) := by
  set V : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hV
  have hV0 : 0 < V := volume_euclideanBall_toReal_pos (0 : Vec d) one_pos
  set Cd : ℝ := (czDilateConst d).toReal with hCd
  have hCd0 : 0 ≤ Cd := ENNReal.toReal_nonneg
  set C2 : ℝ := 4 * 2 ^ d + 2 ^ d * Cd + 4 * (hormanderConst d * 2 ^ (d + 1)) with hC2
  have hC20 : 0 ≤ C2 := by have := hormanderConst_nonneg d; positivity
  set C1 : ℝ := 2 ^ d * V / 8 ^ d with hC1
  have hC10 : 0 < C1 := by positivity
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro K A hKs hKi hA hl2 hgrad f hf hsupp lam hlam
  have hfc : HasCompactSupport f := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec d) 1) (isClosed_tsupport f)
      fun y hy => ?_
    have h := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).mp (hsupp hy)
    rw [sub_zero] at h
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_vecEuclideanNorm y).trans h.le
  have hKh : HormanderKernel K A := ⟨hKs, hKi, hA, hl2, hgrad⟩
  rcases hA.eq_or_lt with hA0 | hApos
  · -- `A = 0`: Chebyshev
    subst hA0
    refine (measure_mono fun x hx => hx.2).trans ?_
    refine (volume_lt_abs_integral_kernel_mul_le hKi hf.continuous hfc hlam).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have := hl2 f hf hfc
    have h0 : 0 ≤ lam⁻¹ ^ 2 := by positivity
    have : lam⁻¹ ^ 2 * ∫ x, (∫ y, K (x - y) * f y) ^ 2 ≤ 0 := by
      have h1 : ∫ x, (∫ y, K (x - y) * f y) ^ 2 ≤ 0 := by simpa using this
      exact mul_nonpos_of_nonneg_of_nonpos h0 h1
    simpa using this
  · set i0 : Fin d := ⟨0, hd⟩ with hi0
    set F : Vec d → Vec d := fun x => Pi.single i0 (f x) with hFdef
    have hFn : ∀ x, vecEuclideanNorm (F x) = |f x| := fun x => vecEuclideanNorm_single i0 _
    have hFk : ∀ x, kconv K i0 F x = ∫ y, K (x - y) * f y := fun x => by
      simp [kconv, hFdef]
    have hFs : ContDiff ℝ (⊤ : ℕ∞) F := by
      refine contDiff_pi.mpr fun j => ?_
      by_cases h : j = i0
      · subst h; simpa [hFdef] using hf
      · simp only [hFdef, Pi.single_apply, h, ite_false]
        exact contDiff_const
    have hFsub : tsupport F ⊆ euclideanBall (0 : Vec d) 1 := by
      refine subset_trans (closure_mono fun x hx => ?_) hsupp
      intro hfx
      apply hx
      simp [hFdef, hfx]
    have hFc : HasCompactSupport F := by
      refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec d) 1) (isClosed_tsupport F)
        fun y hy => ?_
      have h := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).mp (hFsub hy)
      rw [sub_zero] at h
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_le_vecEuclideanNorm y).trans h.le
    set I : Box (Fin d) := rootBox d with hI
    have hFsupp : ∀ x, x ∉ (I : Set (Vec d)) → F x = 0 := by
      intro x hx
      by_contra hne
      exact hx (euclideanBall_one_subset_rootBox d (hFsub (subset_tsupport F hne)))
    have hFi : ∀ i, Continuous fun x => F x i := fun i => (contDiff_pi.mp hFs i).continuous
    have hFI : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)) := fun i =>
      ((hFi i).integrable_of_hasCompactSupport (hasCompactSupport_apply hFc i)).integrableOn
    set m : ℝ := ∫ x, vecEuclideanNorm (F x) with hm
    have hm' : m = ∫ x, |f x| := by simp [hm, hFn]
    have hm0 : 0 ≤ m := integral_nonneg fun _ => vecEuclideanNorm_nonneg _
    set ℓ : ℝ := lam / A with hℓ
    have hℓpos : 0 < ℓ := div_pos hlam hApos
    have hvolI : (volume (I : Set (Vec d))).toReal = 8 ^ d :=
      volume_box_toReal_eq_pow_of_commonWidth I 8 (rootBox_width d)
    have hIm : ∫ x in (I : Set (Vec d)), vecEuclideanNorm (F x) = m := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      simp [hFsupp x hx, vecEuclideanNorm, vecNormSq, vecDot]
    have havg : integralAverage (I : Set (Vec d)) (fun x => vecEuclideanNorm (F x)) =
        (8 ^ d)⁻¹ * m := by
      unfold integralAverage
      rw [hvolI, hIm]
    have hpow : (0 : ℝ) < 8 ^ d := by positivity
    rw [← hm']
    by_cases hcase : integralAverage (I : Set (Vec d)) (fun x => vecEuclideanNorm (F x)) < ℓ
    · obtain ⟨S⟩ := exists_czStopping hd I 8 (rootBox_width d) hFI hcase
      refine (measure_mono fun x (hx : x ∈ euclideanBall (0 : Vec d) 2 ∧ _) =>
        (show lam < |kconv K i0 F x| by rw [hFk]; exact hx.2)).trans
        ((volume_kconv_gt_le_of_stopping hKh hd i0 hFs hFc hFsupp S hlam).trans ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      have hlam' : lam ≠ 0 := hlam.ne'
      have hA' : A ≠ 0 := hApos.ne'
      have heq : 4 * 2 ^ d * A ^ 2 * ℓ * m / lam ^ 2 + 2 ^ d * Cd * m / ℓ +
          4 * (hormanderConst d * (2 ^ (d + 1) * A)) * m / lam = C2 * A / lam * m := by
        rw [hℓ, hC2]
        field_simp
      rw [heq]
      have : 0 ≤ C1 * A / lam * m := by positivity
      calc C2 * A / lam * m ≤ C2 * A / lam * m + C1 * A / lam * m := le_add_of_nonneg_right this
        _ = (C1 + C2) * A / lam * m := by ring
    · push Not at hcase
      rw [havg] at hcase
      have hball : volume (euclideanBall (0 : Vec d) 2) = ENNReal.ofReal (2 ^ d * V) := by
        rw [volume_euclideanBall_eq_unit_mul_of_pos _ (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_mul (by positivity), hV, ENNReal.ofReal_toReal
            (volume_euclideanBall_ne_top _ zero_le_one)]
      refine (measure_mono fun x hx => hx.1).trans ?_
      rw [hball]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : 8 ^ d * ℓ ≤ m := by
        have := mul_le_mul_of_nonneg_left hcase hpow.le
        rwa [← mul_assoc, mul_inv_cancel₀ hpow.ne', one_mul] at this
      have h2 : 2 ^ d * V ≤ C1 * m / ℓ := by
        rw [hC1, div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
        have : 2 ^ d * V * (8 ^ d * ℓ) ≤ 2 ^ d * V * m :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        linarith
      have h3 : C1 * m / ℓ = C1 * A / lam * m := by
        rw [hℓ]; field_simp
      have h4 : 0 ≤ C2 * A / lam * m := by positivity
      calc 2 ^ d * V ≤ C1 * m / ℓ := h2
        _ = C1 * A / lam * m := h3
        _ ≤ C1 * A / lam * m + C2 * A / lam * m := le_add_of_nonneg_right h4
        _ = (C1 + C2) * A / lam * m := by ring

end

end AFree
