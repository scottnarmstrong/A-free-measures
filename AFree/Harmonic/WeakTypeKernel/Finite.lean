module

public import AFree.Harmonic.WeakTypeKernel.Hormander

/-!
# The finite-piece estimate for a mollified Calderón–Zygmund decomposition

For stopping cubes `S` at height `ℓ` and a finite set `s` of cubes, the convolution of the
mollified field `F_a` with the kernel is split into the truncated good part (controlled by the
`L²` hypothesis) and the finitely many mollified bad parts (controlled by the Hörmander estimate
off the exceptional set).
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter PDE PDE.NewtonWeakType
open scoped ENNReal Topology

namespace AFree

noncomputable section

/-- The hypotheses on a convolution kernel: smooth, integrable, with an `L²` bound on smooth
compactly supported functions with constant `A` and the Hörmander gradient condition. -/
structure HormanderKernel {d : ℕ} (K : Vec d → ℝ) (A : ℝ) : Prop where
  /-- The kernel is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) K
  /-- The kernel is integrable. -/
  integrable : Integrable K
  /-- The constant is nonnegative. -/
  nonneg : 0 ≤ A
  /-- The `L²` bound on test functions. -/
  l2 : ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    ∫ x, (∫ y, K (x - y) * f y) ^ 2 ≤ A ^ 2 * ∫ x, f x ^ 2
  /-- The Hörmander gradient condition. -/
  grad : ∀ x : Vec d, x ≠ 0 → ∀ v : Vec d,
    |fderiv ℝ K x v| ≤ A * vecEuclideanNorm v / vecEuclideanNorm x ^ (d + 1)

variable {d : ℕ} {I : Box (Fin d)} {F : Vec d → Vec d} {ℓ : ℝ} {K : Vec d → ℝ} {A : ℝ}

theorem continuous_mollVec_coord {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} (hf : VBdd f) (i : Fin d) :
    Continuous fun y => mollVec a f y i :=
  (contDiff_pi.mp (contDiff_mollVec ha hf) i).continuous

theorem hasCompactSupport_mollVec_coord {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} (hf : VBdd f)
    (i : Fin d) : HasCompactSupport fun y => mollVec a f y i :=
  hasCompactSupport_apply (hasCompactSupport_mollVec ha hf) i

theorem integrable_kconv_term (hKi : Integrable K) {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d}
    (hf : VBdd f) (i : Fin d) (x : Vec d) :
    Integrable fun y => K (x - y) * mollVec a f y i :=
  integrable_kernel_mul hKi (continuous_mollVec_coord ha hf i)
    (hasCompactSupport_mollVec_coord ha hf i) x

variable (S : CZStopping I F ℓ)

theorem kconv_mollVec_decomp (hKi : Integrable K) {a : ℝ} (ha : 0 < a) (hF : VBdd F)
    (s : Finset S.ι) (i : Fin d) (x : Vec d) :
    kconv K i (mollVec a F) x = kconv K i (mollVec a (czTrunc S s)) x +
      ∑ k ∈ s, kconv K i (mollVec a (czBad S k)) x := by
  have hbad := fun k (_ : k ∈ s) => vbdd_czBad S hF k
  have hdec := congrFun (mollVec_decomp S ha hF s)
  unfold kconv
  have e : ∀ y, K (x - y) * mollVec a F y i = K (x - y) * mollVec a (czTrunc S s) y i +
      ∑ k ∈ s, K (x - y) * mollVec a (czBad S k) y i := by
    intro y
    rw [hdec y]
    simp [mul_add, Finset.mul_sum, Finset.sum_apply]
  simp_rw [e]
  rw [integral_add (integrable_kconv_term hKi ha (vbdd_czTrunc S hF s) i x)
    (integrable_finsetSum _ fun k hk => integrable_kconv_term hKi ha (hbad k hk) i x),
    integral_finsetSum _ fun k hk => integrable_kconv_term hKi ha (hbad k hk) i x]

theorem integral_sq_mollVec_coord_le {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} (hf : VBdd f)
    (i : Fin d) : ∫ y, (mollVec a f y i) ^ 2 ≤ ∫ y, vecNormSq (f y) := by
  have h1 : ∫ y, (mollVec a f y i) ^ 2 ≤ ∫ y, (f y i) ^ 2 :=
    integral_sq_wholeSpaceMollify_le ha (hf i)
  refine h1.trans (integral_mono (MemLp.integrable_sq ((hf i).memLp 2)) ?_ fun y => ?_)
  · simp_rw [vecNormSq_eq_sum_sq]
    exact integrable_finsetSum _ fun j _ => MemLp.integrable_sq ((hf j).memLp 2)
  · rw [vecNormSq_eq_sum_sq]
    exact Finset.single_le_sum (f := fun j => f y j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)

/-- The truncated good part is controlled by the `L²` hypothesis and Chebyshev. -/
theorem volume_kconv_trunc_gt_le (hK : HormanderKernel K A) {a : ℝ} (ha : 0 < a) (hF : VBdd F)
    (s : Finset S.ι) (i : Fin d) {c : ℝ} (hc : 0 < c) :
    volume {x | c < |kconv K i (mollVec a (czTrunc S s)) x|} ≤
      ENNReal.ofReal (c⁻¹ ^ 2 * (A ^ 2 * ∫ x, vecNormSq (czTrunc S s x))) := by
  have hv := vbdd_czTrunc S hF s
  refine (volume_lt_abs_integral_kernel_mul_le hK.integrable
    (continuous_mollVec_coord ha hv i) (hasCompactSupport_mollVec_coord ha hv i) hc).trans ?_
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine (hK.l2 _ (contDiff_pi.mp (contDiff_mollVec ha hv) i)
    (hasCompactSupport_mollVec_coord ha hv i)).trans ?_
  exact mul_le_mul_of_nonneg_left (integral_sq_mollVec_coord_le ha hv i) (sq_nonneg _)

/-- The `L¹` norm of a mollified coordinate is at most that of the field. -/
theorem integral_abs_mollVec_coord_le {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} (hf : VBdd f)
    (i : Fin d) : ∫ y, |mollVec a f y i| ≤ ∫ y, vecEuclideanNorm (f y) := by
  have h1 : ∫ y, |mollVec a f y i| ≤ ∫ y, |f y i| := integral_abs_wholeSpaceMollify_le ha (hf i)
  refine h1.trans (integral_mono (hf i).integrable.abs ?_ fun y => abs_apply_le_vecEuclideanNorm _ _)
  exact integrable_vecEuclideanNorm_of_coord f fun j => (hf j).integrable

theorem lintegral_kconv_bad_exterior_le (hK : HormanderKernel K A) [NeZero d] (hF : VBdd F)
    (hFI : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (s : Finset S.ι) {a : ℝ} (ha : 0 < a) (hsa : ∀ k ∈ s, Real.sqrt d * a ≤ czRadius S k)
    (i : Fin d) :
    ∫⁻ x in (czExceptional S)ᶜ,
        ENNReal.ofReal |∑ k ∈ s, kconv K i (mollVec a (czBad S k)) x| ≤
      ENNReal.ofReal (hormanderConst d * (2 ^ (d + 1) * A)) *
        (2 * ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hbad := fun k (_ : k ∈ s) => vbdd_czBad S hF k
  set H : ℝ := hormanderConst d * (2 ^ (d + 1) * A) with hH
  have hH0 : 0 ≤ H := mul_nonneg (hormanderConst_nonneg d) (by have := hK.nonneg; positivity)
  have hmeas : ∀ k ∈ s, AEMeasurable
      (fun x => ENNReal.ofReal |kconv K i (mollVec a (czBad S k)) x|) volume := fun k hk =>
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_integral_kernel_mul hK.integrable (continuous_mollVec_coord ha (hbad k hk) i)
        (hasCompactSupport_mollVec_coord ha (hbad k hk) i)).aestronglyMeasurable.aemeasurable.norm)
  have hper : ∀ k ∈ s, ∫⁻ x in (czExceptional S)ᶜ,
      ENNReal.ofReal |kconv K i (mollVec a (czBad S k)) x| ≤
      ENNReal.ofReal H * ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) := by
    intro k hk
    have hr := czRadius_pos S hd k
    have hr2 : 0 < 2 * czRadius S k := by linarith
    have hsupp : ∀ y, 2 * czRadius S k < vecEuclideanNorm (y - czCenter S k) →
        mollVec a (czBad S k) y i = 0 := by
      intro y hy
      have := mollVec_eq_zero_of_support ha (fun z hz => czBad_eq_zero_of_czRadius_lt hd k hz)
        (x := y) (by linarith [hsa k hk])
      exact congrFun this i
    have hmean : ∫ y, mollVec a (czBad S k) y i = 0 := by
      rw [integral_mollVec_coord ha (hbad k hk) i, integral_czBad_coord hFI k i]
    have h1 := lintegral_exterior_kernel_le hK.smooth hK.integrable hK.nonneg hK.grad hr2
      (continuous_mollVec_coord ha (hbad k hk) i) (hasCompactSupport_mollVec_coord ha (hbad k hk) i)
      hsupp hmean
    have hsub : (czExceptional S)ᶜ ⊆ (euclideanBall (czCenter S k) (2 * (2 * czRadius S k)))ᶜ :=
      compl_subset_compl.mpr (Set.subset_iUnion (fun k => czBigDilate S k) k)
    refine (lintegral_mono_set hsub).trans (h1.trans ?_)
    have h2 := integral_abs_mollVec_coord_le ha (hbad k hk) i
    calc ENNReal.ofReal (hormanderConst d * (2 ^ (d + 1) * A) * ∫ y, |mollVec a (czBad S k) y i|)
        ≤ ENNReal.ofReal (H * ∫ y, vecEuclideanNorm (czBad S k y)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h2 hH0)
      _ = ENNReal.ofReal H * ENNReal.ofReal (∫ y, vecEuclideanNorm (czBad S k y)) :=
          ENNReal.ofReal_mul hH0
      _ = _ := by rw [ofReal_integral_vecEuclideanNorm_czBad hFI k]
  calc ∫⁻ x in (czExceptional S)ᶜ, ENNReal.ofReal |∑ k ∈ s, kconv K i (mollVec a (czBad S k)) x|
      ≤ ∫⁻ x in (czExceptional S)ᶜ,
          ∑ k ∈ s, ENNReal.ofReal |kconv K i (mollVec a (czBad S k)) x| := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => abs_nonneg _]
        exact ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ k ∈ s, ∫⁻ x in (czExceptional S)ᶜ,
          ENNReal.ofReal |kconv K i (mollVec a (czBad S k)) x| :=
        lintegral_finsetSum' _ fun k hk => (hmeas k hk).restrict
    _ ≤ ∑ k ∈ s, ENNReal.ofReal H * ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) :=
        Finset.sum_le_sum hper
    _ = ENNReal.ofReal H * ∑ k ∈ s, ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal H * ∑' k, ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) :=
        mul_le_mul_right (ENNReal.sum_le_tsum _) _
    _ ≤ _ := mul_le_mul_right (tsum_lintegral_vecEuclideanNorm_czBad_le hFI) _

/-- **The finite-piece estimate for the mollified field.** -/
theorem volume_kconv_mollVec_gt_le (hK : HormanderKernel K A) [NeZero d] (hF : VBdd F)
    (hFI : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (s : Finset S.ι) {a : ℝ} (ha : 0 < a) (hsa : ∀ k ∈ s, Real.sqrt d * a ≤ czRadius S k)
    (i : Fin d) {lam : ℝ} (hl : 0 < lam) :
    volume {x | lam < |kconv K i (mollVec a F) x|} ≤
      ENNReal.ofReal ((lam / 2)⁻¹ ^ 2 * (A ^ 2 * ∫ x, vecNormSq (czTrunc S s x))) +
        (volume (czExceptional S) +
          ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal (hormanderConst d * (2 ^ (d + 1) * A)) *
            (2 * ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))))) := by
  have hl2 : 0 < lam / 2 := half_pos hl
  set E := czExceptional S with hE
  set Sg : Vec d → ℝ := fun x => ∑ k ∈ s, kconv K i (mollVec a (czBad S k)) x with hSg
  have hbad := fun k (_ : k ∈ s) => vbdd_czBad S hF k
  have hSgm : AEMeasurable (fun x => ENNReal.ofReal |Sg x|) volume := by
    have : AEStronglyMeasurable Sg volume :=
      (integrable_finsetSum s fun k hk => integrable_integral_kernel_mul hK.integrable
        (continuous_mollVec_coord ha (hbad k hk) i)
        (hasCompactSupport_mollVec_coord ha (hbad k hk) i)).aestronglyMeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable this.aemeasurable.norm
  set G : Set (Vec d) := {x | lam / 2 < |kconv K i (mollVec a (czTrunc S s)) x|} with hG
  set Bd : Set (Vec d) := {x | ENNReal.ofReal (lam / 2) ≤ ENNReal.ofReal |Sg x|} with hBd
  have hsub : {x | lam < |kconv K i (mollVec a F) x|} ⊆ G ∪ (E ∪ (Bd ∩ Eᶜ)) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inr (Or.inl hxE)
    · have hdec := kconv_mollVec_decomp S hK.integrable ha hF s i x
      have hx' : lam < |kconv K i (mollVec a (czTrunc S s)) x| + |Sg x| := by
        calc lam < _ := hx
          _ ≤ _ := by rw [hdec]; exact abs_add_le _ _
      by_cases hg : lam / 2 < |kconv K i (mollVec a (czTrunc S s)) x|
      · exact Or.inl hg
      · refine Or.inr (Or.inr ⟨?_, hxE⟩)
        exact ENNReal.ofReal_le_ofReal (by linarith [not_lt.mp hg])
  have hBdvol : volume (Bd ∩ Eᶜ) ≤
      ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal (hormanderConst d * (2 ^ (d + 1) * A)) *
        (2 * ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)))) := by
    have h1 : volume (Bd ∩ Eᶜ) = (volume.restrict Eᶜ) Bd := by
      rw [Measure.restrict_apply' (measurableSet_czExceptional (S := S)).compl]
    rw [h1]
    have h2 := meas_ge_le_lintegral_div (μ := volume.restrict Eᶜ) hSgm.restrict
      (ε := ENNReal.ofReal (lam / 2)) (by simpa using hl2) ENNReal.ofReal_ne_top
    refine h2.trans ?_
    rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos hl2]
    exact mul_le_mul_right (lintegral_kconv_bad_exterior_le S hK hF hFI s ha hsa i) _
  calc volume {x | lam < |kconv K i (mollVec a F) x|}
      ≤ volume (G ∪ (E ∪ (Bd ∩ Eᶜ))) := measure_mono hsub
    _ ≤ volume G + (volume E + volume (Bd ∩ Eᶜ)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ _ := add_le_add (volume_kconv_trunc_gt_le S hK ha hF s i hl2) (add_le_add le_rfl hBdvol)

end

end AFree
