module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Measure.BallVolume
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-!
# Compactness of convolution with an `L¹` kernel

Convolution with a fixed `L¹` kernel maps `L¹`-bounded sequences to `L¹`-precompact ones, playing the role of [DPR, Lemma 2.1].
-/

@[expose] public section

open MeasureTheory PDE Filter Topology
open scoped Convolution BoundedContinuousFunction

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The convolution `(k ⋆ G)(x) = ∫ k(x - y) · G(y) dy`. -/
def conv (k G : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∫ y, vecDot (k (x - y)) (G y)

/-- The Euclidean dot product as a continuous bilinear map. -/
def dotL : Vec d →L[ℝ] Vec d →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.proj i)
    (ContinuousLinearMap.proj i)

theorem dotL_apply (v w : Vec d) : dotL v w = vecDot v w := by
  simp [dotL, vecDot]

theorem conv_eq_convolution (k G : Vec d → Vec d) :
    conv k G = G ⋆[dotL.flip] k := by
  funext x
  simp [conv, convolution_def, dotL_apply]

theorem integrable_vecEuclideanNorm_comp {G : Vec d → Vec d} (hG : Integrable G) :
    Integrable fun x => vecEuclideanNorm (G x) := by
  refine (hG.norm.const_mul (Real.sqrt d)).mono'
    (continuous_vecEuclideanNorm.comp_aestronglyMeasurable hG.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
  exact vecEuclideanNorm_le_sqrt_natCast_mul_norm _

theorem integrable_conv {k G : Vec d → Vec d} (hk : Integrable k) (hG : Integrable G) :
    Integrable (conv k G) := by
  rw [conv_eq_convolution]
  exact hG.integrable_convolution _ hk

/-- Young: `∫ |k ⋆ G| ≤ ‖k‖₁ ‖G‖₁`. -/
theorem integral_abs_conv_le {k G : Vec d → Vec d} (hk : Integrable k) (hG : Integrable G) :
    ∫ x, |conv k G x| ≤ (∫ x, vecEuclideanNorm (k x)) * ∫ x, vecEuclideanNorm (G x) := by
  set a : Vec d → ℝ := fun x => vecEuclideanNorm (G x) with ha_def
  set b : Vec d → ℝ := fun x => vecEuclideanNorm (k x) with hb_def
  set L := ContinuousLinearMap.mul ℝ ℝ with hL
  have ha := integrable_vecEuclideanNorm_comp hG
  have hb := integrable_vecEuclideanNorm_comp hk
  have hconv : Integrable (a ⋆[L] b) := ha.integrable_convolution L hb
  have hae := ha.ae_convolution_exists L hb
  have hpt : ∀ᵐ x ∂(volume : Measure (Vec d)), |conv k G x| ≤ (a ⋆[L] b) x := by
    filter_upwards [hae] with x hx
    unfold conv
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) hx
      (Filter.Eventually.of_forall fun y => ?_)
    have := abs_vecDot_le_vecEuclideanNorm_mul (k (x - y)) (G y)
    simpa [hL, ha_def, hb_def, mul_comm] using this
  have h3 : ∫ x, (a ⋆[L] b) x = (∫ x, a x) * ∫ x, b x := by
    have := integral_convolution (L := L) ha hb
    simpa [hL] using this
  calc ∫ x, |conv k G x| ≤ ∫ x, (a ⋆[L] b) x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) hconv hpt
    _ = _ := by rw [h3, mul_comm]

theorem vecDot_sub_left (a b c : Vec d) : vecDot (a - b) c = vecDot a c - vecDot b c := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

/-- The convolution integrand with a continuous compactly supported kernel is integrable. -/
theorem integrable_convIntegrand_cc {κ G : Vec d → Vec d} (hκc : Continuous κ)
    (hκs : HasCompactSupport κ) (hG : Integrable G) (x : Vec d) :
    Integrable fun y => vecDot (κ (x - y)) (G y) := by
  have := hκs.convolutionExists_right dotL.flip hG.locallyIntegrable hκc x
  simpa [ConvolutionExistsAt, dotL_apply] using this

theorem exists_bound_cc {κ : Vec d → Vec d} (hκc : Continuous κ) (hκs : HasCompactSupport κ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, vecEuclideanNorm (κ x) ≤ M := by
  have h1 : Continuous fun x => vecEuclideanNorm (κ x) := continuous_vecEuclideanNorm.comp hκc
  have h2 : HasCompactSupport fun x => vecEuclideanNorm (κ x) :=
    hκs.comp_left (g := vecEuclideanNorm) (vecEuclideanNorm_eq_zero_iff.2 rfl)
  obtain ⟨M, hM⟩ := h1.bounded_above_of_compact_support h2
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have := hM x
  rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] at this
  exact this.trans (le_max_left _ _)

theorem abs_conv_cc_le {κ G : Vec d → Vec d} {M : ℝ} (hM : ∀ x, vecEuclideanNorm (κ x) ≤ M)
    (hG : Integrable G) (x : Vec d) :
    |conv κ G x| ≤ M * ∫ y, vecEuclideanNorm (G y) := by
  have hGe := integrable_vecEuclideanNorm_comp hG
  have key : ‖conv κ G x‖ ≤ ∫ y, M * vecEuclideanNorm (G y) := by
    refine norm_integral_le_of_norm_le (hGe.const_mul M) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_vecDot_le_vecEuclideanNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (hM _) (vecEuclideanNorm_nonneg _))
  rw [integral_const_mul, Real.norm_eq_abs] at key
  exact key

theorem continuous_conv_cc {κ G : Vec d → Vec d} (hκc : Continuous κ)
    (hκs : HasCompactSupport κ) (hG : Integrable G) : Continuous (conv κ G) := by
  rw [conv_eq_convolution]
  exact hκs.continuous_convolution_right _ hG.locallyIntegrable hκc

/-- Uniform equicontinuity of `κ ⋆ G` over `G` with bounded `L¹` norm. -/
theorem equicontinuity_conv_cc {κ : Vec d → Vec d} (hκc : Continuous κ)
    (hκs : HasCompactSupport κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ G : Vec d → Vec d, Integrable G → ∀ x x' : Vec d, dist x x' < δ →
      |conv κ G x - conv κ G x'| ≤ ε * ∫ y, vecEuclideanNorm (G y) := by
  have huc := hκs.uniformContinuous_of_continuous hκc
  have hs : 0 < Real.sqrt d + 1 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1 huc (ε / (Real.sqrt d + 1))
    (div_pos hε hs)
  refine ⟨δ, hδ, fun G hG x x' hxx => ?_⟩
  have hGe := integrable_vecEuclideanNorm_comp hG
  have h1 : conv κ G x - conv κ G x' =
      ∫ y, (vecDot (κ (x - y)) (G y) - vecDot (κ (x' - y)) (G y)) := by
    rw [conv, conv, integral_sub (integrable_convIntegrand_cc hκc hκs hG x)
      (integrable_convIntegrand_cc hκc hκs hG x')]
  rw [h1, ← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hGe.const_mul ε) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, ← vecDot_sub_left]
  refine (abs_vecDot_le_vecEuclideanNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right ?_ (vecEuclideanNorm_nonneg _))
  have hd1 : dist (x - y) (x' - y) < δ := by rwa [dist_sub_right]
  have h2 := hδ' hd1
  have h3 := vecEuclideanNorm_le_sqrt_natCast_mul_norm (κ (x - y) - κ (x' - y))
  rw [← dist_eq_norm] at h3
  calc vecEuclideanNorm (κ (x - y) - κ (x' - y))
      ≤ Real.sqrt d * dist (κ (x - y)) (κ (x' - y)) := h3
    _ ≤ Real.sqrt d * (ε / (Real.sqrt d + 1)) :=
        mul_le_mul_of_nonneg_left h2.le (Real.sqrt_nonneg _)
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hs]
        nlinarith [Real.sqrt_nonneg (d : ℝ)]

/-- Young for the difference: `∫ |k ⋆ G - κ ⋆ G| ≤ ‖k - κ‖₁ ‖G‖₁`. -/
theorem integral_abs_conv_sub_le {k κ G : Vec d → Vec d} (hk : Integrable k)
    (hκ : Integrable κ) (hG : Integrable G) :
    ∫ x, |conv k G x - conv κ G x| ≤
      (∫ x, vecEuclideanNorm (k x - κ x)) * ∫ x, vecEuclideanNorm (G x) := by
  have hae := hG.ae_convolution_exists dotL.flip hk
  have hae2 := hG.ae_convolution_exists dotL.flip hκ
  have h : ∀ᵐ x ∂(volume : Measure (Vec d)), conv k G x - conv κ G x = conv (k - κ) G x := by
    filter_upwards [hae, hae2] with x h1 h2
    simp only [ConvolutionExistsAt, ContinuousLinearMap.flip_apply, dotL_apply] at h1 h2
    unfold conv
    rw [← integral_sub h1 h2]
    simp [vecDot_sub_left]
  calc ∫ x, |conv k G x - conv κ G x| = ∫ x, |conv (k - κ) G x| :=
        integral_congr_ae (by filter_upwards [h] with x hx; rw [hx])
    _ ≤ _ := integral_abs_conv_le (hk.sub hκ) hG

/-- `C_c` approximation of an `L¹` kernel, measured in the Euclidean norm. -/
theorem exists_cc_approx {k : Vec d → Vec d} (hk : Integrable k) (q : ℕ) :
    ∃ κ : Vec d → Vec d, Continuous κ ∧ HasCompactSupport κ ∧ Integrable κ ∧
      ∫ x, vecEuclideanNorm (k x - κ x) ≤ 1 / ((q : ℝ) + 1) := by
  have hs : 0 < Real.sqrt d + 1 := by positivity
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  obtain ⟨κ, hκs, hκ, hκc, hκi⟩ := hk.exists_hasCompactSupport_integral_sub_le
    (ε := 1 / (((q : ℝ) + 1) * (Real.sqrt d + 1))) (by positivity)
  refine ⟨κ, hκc, hκs, hκi, ?_⟩
  have hint : Integrable fun x => ‖k x - κ x‖ := (hk.sub hκi).norm
  have h1 : ∫ x, vecEuclideanNorm (k x - κ x) ≤ ∫ x, Real.sqrt d * ‖k x - κ x‖ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => vecEuclideanNorm_nonneg _)
      (hint.const_mul _)
      (Filter.Eventually.of_forall fun x => vecEuclideanNorm_le_sqrt_natCast_mul_norm _)
  rw [integral_const_mul] at h1
  refine h1.trans ?_
  calc Real.sqrt d * ∫ x, ‖k x - κ x‖
      ≤ Real.sqrt d * (1 / (((q : ℝ) + 1) * (Real.sqrt d + 1))) :=
        mul_le_mul_of_nonneg_left hκ (Real.sqrt_nonneg _)
    _ ≤ 1 / ((q : ℝ) + 1) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hq]
        nlinarith [Real.sqrt_nonneg (d : ℝ)]

/-- Triangle inequality for set integrals of absolute differences. -/
theorem setIntegral_abs_sub_le {s : Set (Vec d)} {a b c e : Vec d → ℝ}
    (ha : IntegrableOn a s) (hb : IntegrableOn b s) (hc : IntegrableOn c s)
    (he : IntegrableOn e s) :
    ∫ x in s, |a x - e x| ≤
      (∫ x in s, |a x - b x|) + (∫ x in s, |b x - c x|) + ∫ x in s, |c x - e x| := by
  have i1 : IntegrableOn (fun x => |a x - b x|) s := (ha.sub hb).abs
  have i2 : IntegrableOn (fun x => |b x - c x|) s := (hb.sub hc).abs
  have i3 : IntegrableOn (fun x => |c x - e x|) s := (hc.sub he).abs
  have i12 : IntegrableOn (fun x => |a x - b x| + |b x - c x|) s := i1.add i2
  rw [← integral_add i1 i2, ← integral_add i12 i3]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (i12.add i3) (Filter.Eventually.of_forall fun x => ?_)
  have h3 : |a x - e x| ≤ |a x - b x| + |b x - e x| := abs_sub_le _ _ _
  have h4 : |b x - e x| ≤ |b x - c x| + |c x - e x| := abs_sub_le _ _ _
  linarith

/-- Uniform-on-`K` equicontinuity and boundedness of `κ ⋆ F_j`, then Arzelà-Ascoli: the family
`j ↦ κ ⋆ F_j` has a finite `δ`-net, uniformly on the closed unit sup-ball. -/
theorem exists_finite_sup_net {κ : Vec d → Vec d} (hκc : Continuous κ)
    (hκs : HasCompactSupport κ) {M C : ℝ} (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (hM : ∀ x, vecEuclideanNorm (κ x) ≤ M) {F : ℕ → Vec d → Vec d}
    (hF : ∀ j, Integrable (F j)) (hC : ∀ j, ∫ x, vecEuclideanNorm (F j x) ≤ C) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ J : Set ℕ, J.Finite ∧ ∀ j, ∃ i ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec d) 1,
      |conv κ (F j) x - conv κ (F i) x| ≤ δ := by
  set K : Set (Vec d) := Metric.closedBall (0 : Vec d) 1 with hK
  have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  let P : ℕ → (K →ᵇ ℝ) := fun j =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => conv κ (F j) x, (continuous_conv_cc hκc hκs (hF j)).comp continuous_subtype_val⟩
  have hP : ∀ j (x : K), P j x = conv κ (F j) x := fun j x => rfl
  have hbound : ∀ j x, |conv κ (F j) x| ≤ M * C := fun j x =>
    (abs_conv_cc_le hM (hF j) x).trans (mul_le_mul_of_nonneg_left (hC j) hM0)
  have hequi : Equicontinuous ((↑) : Set.range P → K → ℝ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_pair]
    intro ε₁ hε₁
    obtain ⟨δ', hδ', hδ''⟩ := equicontinuity_conv_cc hκc hκs
      (show 0 < ε₁ / (2 * (C + 1)) by positivity)
    refine ⟨Metric.ball x₀ (δ' / 2), Metric.ball_mem_nhds _ (by positivity), ?_⟩
    intro x hx x' hx' ⟨_, j, rfl⟩
    have hxx : dist (x : Vec d) x' < δ' := by
      have := dist_triangle_right (x : Vec d) x' x₀
      rw [Metric.mem_ball] at hx hx'
      have h1 : dist (x : Vec d) x₀ < δ' / 2 := hx
      have h2 : dist (x' : Vec d) x₀ < δ' / 2 := hx'
      linarith
    have := hδ'' (F j) (hF j) x x' hxx
    rw [Real.dist_eq]
    show |conv κ (F j) x - conv κ (F j) x'| < ε₁
    calc _ ≤ ε₁ / (2 * (C + 1)) * ∫ y, vecEuclideanNorm (F j y) := this
      _ ≤ ε₁ / (2 * (C + 1)) * C :=
          mul_le_mul_of_nonneg_left (hC j) (by positivity)
      _ < ε₁ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  have hcpt := BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) (M * C))
    (isCompact_closedBall _ _) (Set.range P)
    (fun f x ⟨j, hj⟩ => by
      rw [← hj, hP, Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hbound j x) hequi
  have hTB : TotallyBounded (Set.range P) := hcpt.totallyBounded.subset subset_closure
  obtain ⟨t, hts, htf, hcov⟩ := hTB.exists_subset (U := {p | dist p.1 p.2 < δ})
    (Metric.dist_mem_uniformity hδ)
  obtain ⟨J, -, hJf, hJ⟩ := (Set.exists_subset_image_finite_and (f := P) (s := Set.univ)
    (p := fun t => Set.range P ⊆ ⋃ y ∈ t,
      {x | (x, y) ∈ {p : (K →ᵇ ℝ) × (K →ᵇ ℝ) | dist p.1 p.2 < δ}})).1
    ⟨t, by rwa [Set.image_univ], htf, hcov⟩
  refine ⟨J, hJf, fun j => ?_⟩
  have h1 := hJ ⟨j, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at h1
  obtain ⟨y, hy, hdist⟩ := h1
  obtain ⟨i, hi, rfl⟩ := hy
  refine ⟨i, hi, fun x hx => ?_⟩
  have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := P j) (g := P i) (⟨x, hx⟩ : K)
  rw [Real.dist_eq, hP, hP] at h2
  exact h2.trans hdist.le

/-- A finite net, in `L¹(B_1)`, for the family `k ⋆ F_j`. -/
theorem exists_finite_L1_net {k : Vec d → Vec d} (hk : Integrable k) {F : ℕ → Vec d → Vec d}
    (hF : ∀ j, Integrable (F j)) {C : ℝ} (hC : ∀ j, ∫ x, vecEuclideanNorm (F j x) ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : Set ℕ, J.Finite ∧ ∀ j, ∃ i ∈ J,
      ∫ x in euclideanBall (0 : Vec d) 1, |conv k (F j) x - conv k (F i) x| ≤ ε := by
  set B := euclideanBall (0 : Vec d) 1 with hB
  have hC0 : 0 ≤ C := (integral_nonneg fun x => vecEuclideanNorm_nonneg _).trans (hC 0)
  set η := ε / 3 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨q, hq⟩ := exists_nat_gt (C / η)
  have hq1 : C / ((q : ℝ) + 1) ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hη0] at hq
    nlinarith
  obtain ⟨κ, hκc, hκs, hκi, hκ⟩ := exists_cc_approx hk q
  obtain ⟨M, hM0, hM⟩ := exists_bound_cc hκc hκs
  have hvB : (volume B).toReal < (volume B).toReal + 1 := by linarith
  have hvB0 : 0 ≤ (volume B).toReal := ENNReal.toReal_nonneg
  obtain ⟨J, hJf, hJ⟩ := exists_finite_sup_net hκc hκs hM0 hC0 hM hF hC
    (δ := η / ((volume B).toReal + 1)) (by positivity)
  refine ⟨J, hJf, fun j => ⟨(hJ j).choose, (hJ j).choose_spec.1, ?_⟩⟩
  set i := (hJ j).choose
  have hi := (hJ j).choose_spec.2
  have hB1 : B ⊆ Metric.closedBall (0 : Vec d) 1 := fun x hx =>
    Metric.ball_subset_closedBall (euclideanBall_subset_supBall one_pos hx)
  have hBvol : volume B ≠ ⊤ := volume_euclideanBall_ne_top _ zero_le_one
  have hmeas : MeasurableSet B := measurableSet_euclideanBall _ _
  have iK : ∀ l, IntegrableOn (conv k (F l)) B := fun l =>
    (integrable_conv hk (hF l)).integrableOn
  have iκ : ∀ l, IntegrableOn (conv κ (F l)) B := fun l =>
    (integrable_conv hκi (hF l)).integrableOn
  have hside : ∀ l, ∫ x in B, |conv k (F l) x - conv κ (F l) x| ≤ η := by
    intro l
    refine le_trans ?_ hq1
    calc ∫ x in B, |conv k (F l) x - conv κ (F l) x|
        ≤ ∫ x, |conv k (F l) x - conv κ (F l) x| :=
          setIntegral_le_integral (((integrable_conv hk (hF l)).sub
            (integrable_conv hκi (hF l))).abs)
            (Filter.Eventually.of_forall fun x => abs_nonneg _)
      _ ≤ (∫ x, vecEuclideanNorm (k x - κ x)) * ∫ x, vecEuclideanNorm (F l x) :=
          integral_abs_conv_sub_le hk hκi (hF l)
      _ ≤ 1 / ((q : ℝ) + 1) * C :=
          mul_le_mul hκ (hC l) (integral_nonneg fun x => vecEuclideanNorm_nonneg _)
            (by positivity)
      _ = C / ((q : ℝ) + 1) := by ring
  have hmid : ∫ x in B, |conv κ (F j) x - conv κ (F i) x| ≤ η := by
    calc ∫ x in B, |conv κ (F j) x - conv κ (F i) x|
        ≤ ∫ x in B, η / ((volume B).toReal + 1) :=
          setIntegral_mono_on ((iκ j).sub (iκ i)).abs (integrableOn_const hBvol) hmeas
            (fun x hx => hi x (hB1 hx))
      _ = η / ((volume B).toReal + 1) * (volume B).toReal := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
      _ ≤ η := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have hs' : ∫ x in B, |conv κ (F i) x - conv k (F i) x| ≤ η := by
    have e : (fun x => |conv κ (F i) x - conv k (F i) x|) =
        fun x => |conv k (F i) x - conv κ (F i) x| := funext fun x => abs_sub_comm _ _
    rw [e]; exact hside i
  have := setIntegral_abs_sub_le (iK j) (iκ j) (iκ i) (iK i)
  linarith [hside j]

/-- Compactness of convolution with an `L¹` kernel: for `k` integrable and
`F_j` integrable with `‖F_j‖_{L¹} ≤ C`, a subsequence of `k ⋆ F_j` converges in `L¹(B_1)`. -/
theorem exists_subseq_tendsto_conv {k : Vec d → Vec d} (hk : Integrable k)
    {F : ℕ → Vec d → Vec d} (hF : ∀ j, Integrable (F j)) {C : ℝ}
    (hC : ∀ j, ∫ x, vecEuclideanNorm (F j x) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : Vec d → ℝ, IntegrableOn g (euclideanBall (0 : Vec d) 1) ∧
      Tendsto (fun i => ∫ x in euclideanBall (0 : Vec d) 1, |conv k (F (φ i)) x - g x|) atTop
        (𝓝 0) := by
  set B := euclideanBall (0 : Vec d) 1 with hB
  have hint : ∀ j, Integrable (conv k (F j)) (volume.restrict B) := fun j =>
    (integrable_conv hk (hF j)).restrict
  let u : ℕ → (Vec d →₁[volume.restrict B] ℝ) := fun j => (hint j).toL1 _
  have hdist : ∀ i j, dist (u i) (u j) = ∫ x in B, |conv k (F i) x - conv k (F j) x| := by
    intro i j
    have e : u i - u j =
        ((hint i).sub (hint j)).toL1 (conv k (F i) - conv k (F j)) := rfl
    rw [_root_.dist_eq_norm, e, L1.norm_of_fun_eq_integral_norm]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hTB : TotallyBounded (Set.range u) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨J, hJf, hJ⟩ := exists_finite_L1_net hk hF hC (half_pos hε)
    refine ⟨u '' J, hJf.image _, ?_⟩
    rintro _ ⟨j, rfl⟩
    obtain ⟨i, hi, hd⟩ := hJ j
    simp only [Set.mem_iUnion, Metric.mem_ball]
    exact ⟨u i, ⟨i, hi, rfl⟩, by rw [hdist]; linarith⟩
  have hcpt : IsCompact (closure (Set.range u)) :=
    hTB.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨a, -, φ, hφ, ht⟩ := hcpt.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨φ, hφ, a, L1.integrable_coeFn a, ?_⟩
  have key : ∀ i, ∫ x in B, |conv k (F (φ i)) x - a x| = dist (u (φ i)) a := by
    intro i
    rw [_root_.dist_eq_norm, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (u (φ i)) a, Integrable.coeFn_toL1 (hint (φ i))] with x h1 h2
    rw [h1, Pi.sub_apply, Real.norm_eq_abs]
    simp only [u, h2]
  simp_rw [key]
  exact (tendsto_iff_dist_tendsto_zero.1 ht)

end

end AFree
