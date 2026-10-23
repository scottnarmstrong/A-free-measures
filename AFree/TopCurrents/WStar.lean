module

public import AFree.TopCurrents.IbpMinor
public import AFree.TopCurrents.SmoothDense

/-!
# Weak-* continuity of minors
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE

variable {d m : ℕ}

/-- `|∫ h M| ≤ C^s ∫ |h|` for the minor of a Euclidean `C`-Lipschitz tuple. -/
theorem abs_integral_mul_minor_le {s : ℕ} {C : ℝ≥0} {F : Fin m → Vec d → ℝ}
    (hF : ∀ i, IsEuclLipschitzWith C (F i)) (r : Fin s → Fin m) (c : Fin s → Fin d)
    (hc : Function.Injective c) {h : Vec d → ℝ} (hh : Integrable h volume) :
    |∫ x, h x * minorDet F r c x| ≤ (C : ℝ) ^ s * ∫ x, |h x| := by
  have := norm_integral_le_of_norm_le (hh.abs.const_mul ((C : ℝ) ^ s))
    (f := fun x => h x * minorDet F r c x) (by
      filter_upwards [ae_abs_minorDet_le hF r c hc] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |h x| * |minorDet F r c x| ≤ |h x| * (C : ℝ) ^ s :=
            mul_le_mul_of_nonneg_left hx (abs_nonneg _)
        _ = _ := mul_comm _ _)
  rwa [integral_const_mul, Real.norm_eq_abs] at this

/-- The term `∫ ∂_v φ F^n_i M' (F^n) → ∫ ∂_v φ F_i M'(F)` given the induction hypothesis. -/
private theorem wstar_term {s : ℕ} {C : ℝ≥0} {Fn : ℕ → Fin m → Vec d → ℝ} {F : Fin m → Vec d → ℝ}
    (hFn : ∀ n i, IsEuclLipschitzWith C (Fn n i))
    (hlim : ∀ x i, Tendsto (fun n => Fn n i x) atTop (𝓝 (F i x)))
    (hF : ∀ i, IsEuclLipschitzWith C (F i))
    {r : Fin s → Fin m} {c : Fin s → Fin d} (hc : Function.Injective c)
    (hIH : ∀ g : Vec d → ℝ, Integrable g volume →
      Tendsto (fun n => ∫ x, g x * minorDet (Fn n) r c x) atTop
        (𝓝 (∫ x, g x * minorDet F r c x)))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (v : Vec d) (i : Fin m) :
    Tendsto (fun n => ∫ x, fderiv ℝ φ x v * Fn n i x * minorDet (Fn n) r c x) atTop
      (𝓝 (∫ x, fderiv ℝ φ x v * F i x * minorDet F r c x)) := by
  have hdφ : Continuous fun x => fderiv ℝ φ x v :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsupp : HasCompactSupport fun x => fderiv ℝ φ x v := hφc.fderiv_apply ℝ v
  have hcont : ∀ n, Continuous (Fn n i) := fun n => MetricCurrents.Moll.continuous_of_eucl (hFn n i)
  have hFc : Continuous (F i) := MetricCurrents.Moll.continuous_of_eucl (hF i)
  have hcs : ∀ G : Vec d → ℝ, Continuous G → Integrable (fun x => fderiv ℝ φ x v * G x) volume :=
    fun G hG => (hdφ.mul hG).integrable_of_hasCompactSupport hsupp.mul_right
  set θn : ℕ → Vec d → ℝ := fun n x => fderiv ℝ φ x v * Fn n i x with hθn
  set θ : Vec d → ℝ := fun x => fderiv ℝ φ x v * F i x with hθ
  have hθI : Integrable θ volume := hcs _ hFc
  have hθnI : ∀ n, Integrable (θn n) volume := fun n => hcs _ (hcont n)
  have hsplit : ∀ n, ∫ x, θn n x * minorDet (Fn n) r c x =
      (∫ x, (θn n x - θ x) * minorDet (Fn n) r c x) + ∫ x, θ x * minorDet (Fn n) r c x := by
    intro n
    have hA := integrable_mul_minorDet (hFn n) r c hc ((hθnI n).sub hθI)
    have hB := integrable_mul_minorDet (hFn n) r c hc hθI
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_add hA hB)
    show θn n x * _ = (θn n x - θ x) * _ + θ x * _
    ring
  -- the first term tends to zero
  obtain ⟨B, hB⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : Vec d)
  have hunif := (locunif (F := fun n => Fn n i) (fun n => hFn n i) (fun x => hlim x i)).2
    (Metric.closedBall 0 B) Metric.isBounded_closedBall
  have hev : ∀ᶠ n in atTop, ∀ x ∈ Metric.closedBall (0 : Vec d) B, dist (F i x) (Fn n i x) < 1 :=
    Metric.tendstoUniformlyOn_iff.1 hunif 1 one_pos
  have hdφz : ∀ x, x ∉ Metric.closedBall (0 : Vec d) B → fderiv ℝ φ x v = 0 := by
    intro x hx
    by_contra h
    have : fderiv ℝ φ x ≠ 0 := fun h0 => h (by rw [h0]; rfl)
    exact hx (hB (support_fderiv_subset ℝ this))
  have hbI : Integrable (fun x => ‖fderiv ℝ φ x v‖) volume :=
    hdφ.norm.integrable_of_hasCompactSupport hsupp.norm
  have hDCT : Tendsto (fun n => ∫ x, |θn n x - θ x|) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun n x => |θn n x - θ x|) (f := fun _ => (0 : ℝ)) (fun x => ‖fderiv ℝ φ x v‖)
      (Eventually.of_forall fun n =>
        ((hdφ.mul (hcont n)).sub (hdφ.mul hFc)).abs.aestronglyMeasurable)
      (by
        filter_upwards [hev] with n hn
        refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_abs]
        by_cases hx : x ∈ Metric.closedBall (0 : Vec d) B
        · have h1 := hn x hx
          rw [Real.dist_eq] at h1
          simp only [hθn, hθ]
          rw [← mul_sub, abs_mul, Real.norm_eq_abs]
          calc |fderiv ℝ φ x v| * |Fn n i x - F i x| ≤ |fderiv ℝ φ x v| * 1 := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                rw [abs_sub_comm]; exact h1.le
            _ = _ := by rw [mul_one]
        · simp [hθn, hθ, hdφz x hx])
      hbI
      (Eventually.of_forall fun x => by
        have h : Tendsto (fun n => θn n x) atTop (𝓝 (θ x)) :=
          (tendsto_const_nhds (x := fderiv ℝ φ x v)).mul (hlim x i)
        simpa using (h.sub_const (θ x)).abs)
    simpa using this
  have h1 : Tendsto (fun n => ∫ x, (θn n x - θ x) * minorDet (Fn n) r c x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hDCT.const_mul ((C : ℝ) ^ s))
    rw [Real.norm_eq_abs]
    exact abs_integral_mul_minor_le (hFn n) r c hc ((hθnI n).sub hθI)
  have h2 := hIH θ hθI
  have := h1.add h2
  rw [zero_add] at this
  refine this.congr fun n => ?_
  rw [hsplit n]

/-- Step 1: the claim for `g = φ ∈ C¹_c`, given the claim for
minors of size `s`. -/
theorem wstar_smooth_test_function {s : ℕ} {C : ℝ≥0} {Fn : ℕ → Fin m → Vec d → ℝ}
    {F : Fin m → Vec d → ℝ} (hFn : ∀ n i, IsEuclLipschitzWith C (Fn n i))
    (hlim : ∀ x i, Tendsto (fun n => Fn n i x) atTop (𝓝 (F i x)))
    (hF : ∀ i, IsEuclLipschitzWith C (F i))
    (hIH : ∀ (r : Fin s → Fin m) (c : Fin s → Fin d), Function.Injective c →
      ∀ g : Vec d → ℝ, Integrable g volume →
        Tendsto (fun n => ∫ x, g x * minorDet (Fn n) r c x) atTop
          (𝓝 (∫ x, g x * minorDet F r c x)))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (r : Fin (s + 1) → Fin m) (c : Fin (s + 1) → Fin d) (hc : Function.Injective c) :
    Tendsto (fun n => ∫ x, φ x * minorDet (Fn n) r c x) atTop
      (𝓝 (∫ x, φ x * minorDet F r c x)) := by
  rw [ibpminor hF hφ hφc r c hc]
  refine Tendsto.congr (fun n => (ibpminor (hFn n) hφ hφc r c hc).symm) ?_
  refine (tendsto_finsetSum _ fun b _ => ?_).neg
  refine Tendsto.const_mul _ ?_
  have hcb : Function.Injective (c ∘ b.succAbove) := hc.comp Fin.succAbove_right_injective
  exact wstar_term hFn hlim hF hcb (hIH (r ∘ Fin.succ) (c ∘ b.succAbove) hcb) hφ hφc _ (r 0)

/-- Weak-* continuity of minors: if the components of `F^n` are Euclidean `C`-Lipschitz and
`F^n → F` pointwise, then `F` is `C`-Lipschitz and `∫ g M_{I,J}(F^n) → ∫ g M_{I,J}(F)` for every
`g ∈ L¹` and every minor (rows `r`, injective columns `c`). -/
theorem wstar {C : ℝ≥0} {Fn : ℕ → Fin m → Vec d → ℝ} {F : Fin m → Vec d → ℝ}
    (hFn : ∀ n i, IsEuclLipschitzWith C (Fn n i))
    (hlim : ∀ x i, Tendsto (fun n => Fn n i x) atTop (𝓝 (F i x))) :
    (∀ i, IsEuclLipschitzWith C (F i)) ∧
      ∀ (s : ℕ) (r : Fin s → Fin m) (c : Fin s → Fin d), Function.Injective c →
        ∀ g : Vec d → ℝ, Integrable g volume →
          Tendsto (fun n => ∫ x, g x * minorDet (Fn n) r c x) atTop
            (𝓝 (∫ x, g x * minorDet F r c x)) := by
  have hF : ∀ i, IsEuclLipschitzWith C (F i) := fun i =>
    (locunif (F := fun n => Fn n i) (fun n => hFn n i) (fun x => hlim x i)).1
  refine ⟨hF, fun s => ?_⟩
  induction s with
  | zero =>
    intro r c hc g hg
    have h1 : ∀ (G : Fin m → Vec d → ℝ) x, minorDet G r c x = 1 := fun G x => by
      simp [minorDet]
    simp only [h1, mul_one]
    exact tendsto_const_nhds
  | succ s ih =>
    intro r c hc g hg
    rw [Metric.tendsto_atTop]
    intro ε hε
    set K : ℝ := (C : ℝ) ^ (s + 1) with hK
    have hK0 : 0 ≤ K := by positivity
    obtain ⟨φ, hφ, hφint⟩ := smoothdense hg (η := ε / (4 * (K + 1))) (by positivity)
    have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by norm_num)
    have hφI : Integrable φ volume := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
      (wstar_smooth_test_function hFn hlim hF ih hφ1 hφ.2.1 r c hc) (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hbn := hN n hn
    have hgφ : Integrable (fun x => g x - φ x) volume := hg.sub hφI
    have e1 : ∀ G : Fin m → Vec d → ℝ, (∀ i, IsEuclLipschitzWith C (G i)) →
        ∫ x, (g x - φ x) * minorDet G r c x =
          (∫ x, g x * minorDet G r c x) - ∫ x, φ x * minorDet G r c x := by
      intro G hG
      simp_rw [sub_mul]
      exact integral_sub (integrable_mul_minorDet hG r c hc hg)
        (integrable_mul_minorDet hG r c hc hφI)
    have b1 : ∀ G : Fin m → Vec d → ℝ, (∀ i, IsEuclLipschitzWith C (G i)) →
        |∫ x, (g x - φ x) * minorDet G r c x| ≤ ε / 4 := by
      intro G hG
      refine (abs_integral_mul_minor_le hG r c hc hgφ).trans ?_
      have h2 : ∫ x, |g x - φ x| ≤ ε / (4 * (K + 1)) := hφint.le
      calc K * ∫ x, |g x - φ x| ≤ K * (ε / (4 * (K + 1))) :=
            mul_le_mul_of_nonneg_left h2 hK0
        _ ≤ ε / 4 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [hε]
    have hb1 := b1 (Fn n) (hFn n)
    have hb2 := b1 F hF
    rw [e1 _ (hFn n)] at hb1
    rw [e1 _ hF] at hb2
    rw [Real.dist_eq] at hbn ⊢
    rw [abs_lt] at hbn ⊢
    rw [abs_le] at hb1 hb2
    constructor <;> linarith [hbn.1, hbn.2, hb1.1, hb1.2, hb2.1, hb2.2]

end AFree
