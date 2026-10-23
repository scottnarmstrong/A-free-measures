module

public import AFree.Harmonic.Kernel.Dyadic
public import AFree.Harmonic.Kernel.TsumL1

/-!
# Integrable kernels of negative-order symbols

For `m ∈ S^{-s}`, `s > 0`, the kernel `K = Σ_l K_l` of the dyadic pieces converges in `L¹`, and
`vecMultiplier m f = K ⋆ f` for Schwartz `f`.
-/

@[expose] public section

open MeasureTheory PDE Filter
open scoped SchwartzMap ContDiff Topology

namespace AFree

noncomputable section

variable {d : ℕ}

theorem continuous_fourierChar_vecDot (x : Vec d) :
    Continuous (fun ξ : Vec d => Real.fourierChar (vecDot ξ x)) := by
  refine Real.continuous_fourierChar.comp ?_
  unfold vecDot; fun_prop

theorem integrable_fourierChar_smul {g : Vec d → ℂ} (hg : Integrable g) (x : Vec d) :
    Integrable (fun ξ : Vec d => Real.fourierChar (vecDot ξ x) • g ξ) := by
  refine hg.norm.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · exact ((continuous_fourierChar_vecDot x).aestronglyMeasurable).smul hg.1
  · simp

/-- Pointwise formula for a multiplier with temperate-growth symbol. -/
theorem vecMultiplier_apply_integral {T : Vec d → ℂ} (hT : T.HasTemperateGrowth)
    (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    vecMultiplier T f x = ∫ ξ, Real.fourierChar (vecDot ξ x) • (T ξ * vecFourier f ξ) := by
  have h := congrFun (vecFourierInv_vecFourier (vecMultiplier T f)) x
  rw [← h, vecFourierInv_def]
  congr 1
  funext ξ
  rw [vecFourier_vecMultiplier hT]

theorem integrable_symbol_mul_vecFourier {T : Vec d → ℂ} (hT : T.HasTemperateGrowth)
    (f : 𝓢(Vec d, ℂ)) : Integrable (fun ξ => T ξ * vecFourier f ξ) := by
  have : (fun ξ => T ξ * vecFourier f ξ) = ⇑(vecFourierCLM (vecMultiplier T f)) := by
    rw [vecFourier_coe]; funext ξ; rw [vecFourier_vecMultiplier hT]
  rw [this]; exact (vecFourierCLM _).integrable

/-! ### Dyadic kernels as Schwartz functions -/

theorem lpKernel_eq {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ) :
    lpKernel m l = ⇑(vecFourierInvCLM (lpSymS hm l)) :=
  (vecFourierInv_coe (lpSymS hm l)).symm

theorem integrable_lpKernel {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ) :
    Integrable (lpKernel m l) := by
  rw [lpKernel_eq hm]; exact (vecFourierInvCLM _).integrable

theorem vecFourier_lpKernel {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ) :
    vecFourier (lpKernel m l) = lpSym m l := by
  have := vecFourier_vecFourierInv (lpSymS hm l)
  exact this

theorem lpSym_hasTemperateGrowth {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ) :
    (lpSym m l).HasTemperateGrowth := (lpSymS hm l).hasTemperateGrowth

theorem vecMultiplier_lpSym {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (l : ℕ)
    (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    vecMultiplier (lpSym m l) f x = ∫ y, lpKernel m l (x - y) * f y := by
  have h := vecMultiplier_vecFourier_apply (vecFourierInvCLM (lpSymS hm l)) f x
  have e1 : vecFourier ⇑(vecFourierInvCLM (lpSymS hm l)) = lpSym m l := by
    rw [← lpKernel_eq hm l]; exact vecFourier_lpKernel hm l
  rw [e1] at h
  rw [h]
  simp only [← lpKernel_eq hm l]

/-! ### The negative-order kernel -/

/-- The kernel `K = Σ_l K_l` of a symbol of negative order. -/
def negKernel (m : Vec d → ℂ) : Vec d → ℂ := fun x => ∑' l, lpKernel m l x

theorem summable_integral_norm_lpKernel {s : ℝ} (hs : 0 < s) {m : Vec d → ℂ}
    (hm : IsSymbol (-s) m) : Summable fun l => ∫ x, ‖lpKernel m l x‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_norm_lpKernel_le hs.le hm
  have hρ : (2 : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hρ0 : 0 ≤ (2 : ℝ) ^ (-s) := by positivity
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun x => norm_nonneg _)
    (fun l => hC (l + 1) (by omega)) ?_
  have := (summable_geometric_of_lt_one hρ0 hρ).mul_left (C * (2 : ℝ) ^ (-s))
  refine this.congr fun l => ?_
  ring

theorem integrable_negKernel {s : ℝ} (hs : 0 < s) {m : Vec d → ℂ} (hm : IsSymbol (-s) m) :
    Integrable (negKernel m) :=
  integrable_tsum_of_summable_integral (fun l => integrable_lpKernel hm.1 l)
    (summable_integral_norm_lpKernel hs hm)

/-! ### The convolution representation -/

theorem continuous_vecFourier (f : 𝓢(Vec d, ℂ)) : Continuous (vecFourier f) := by
  rw [← vecFourier_coe]; exact (vecFourierCLM f).continuous

/-- Partial sums of the multipliers of the dyadic pieces are the truncated multipliers. -/
theorem sum_vecMultiplier_lpSym {m : Vec d → ℂ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (L : ℕ)
    (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    ∑ l ∈ Finset.range (L + 1), vecMultiplier (lpSym m l) f x =
      ∫ ξ, Real.fourierChar (vecDot ξ x) • ((m ξ * (lpCut L ξ : ℂ)) * vecFourier f ξ) := by
  simp_rw [vecMultiplier_apply_integral (lpSym_hasTemperateGrowth hm _)]
  rw [← integral_finsetSum]
  · congr 1
    funext ξ
    rw [← Finset.smul_sum]
    congr 1
    simp [lpSym, lpCut, Finset.sum_mul, Finset.mul_sum, Complex.ofReal_sum]
  · intro l _
    exact integrable_fourierChar_smul (integrable_symbol_mul_vecFourier
      (lpSym_hasTemperateGrowth hm l) f) x

theorem tendsto_sum_vecMultiplier_lpSym {m : Vec d → ℂ} (hm : m.HasTemperateGrowth)
    (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    Tendsto (fun L => ∑ l ∈ Finset.range (L + 1), vecMultiplier (lpSym m l) f x) atTop
      (𝓝 (vecMultiplier m f x)) := by
  simp_rw [sum_vecMultiplier_lpSym hm.1]
  rw [vecMultiplier_apply_integral hm]
  refine tendsto_integral_of_dominated_convergence (fun ξ => ‖m ξ * vecFourier f ξ‖)
    (fun L => ?_) (integrable_symbol_mul_vecFourier hm f).norm (fun L => ?_) ?_
  · refine (((continuous_fourierChar_vecDot x).smul ?_)).aestronglyMeasurable
    exact (hm.1.continuous.mul (Complex.continuous_ofReal.comp
      (contDiff_lpCut L).continuous)).mul (continuous_vecFourier f)
  · refine Filter.Eventually.of_forall fun ξ => ?_
    simp only [Circle.norm_smul]
    rw [mul_right_comm, norm_mul, norm_mul (m ξ), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (lpCut_nonneg L ξ)]
    have h1 := lpCut_le_one L ξ
    have h2 : 0 ≤ ‖m ξ‖ * ‖vecFourier f ξ‖ := by positivity
    nlinarith
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have h1 : Tendsto (fun L => ((lpCut L ξ : ℝ) : ℂ)) atTop (𝓝 1) := by
      have := (Complex.continuous_ofReal.tendsto 1).comp (tendsto_lpCut ξ)
      simpa [Function.comp_def] using this
    have h2 := ((h1.const_mul (m ξ)).mul_const (vecFourier f ξ))
    have h3 := h2.const_smul (Real.fourierChar (vecDot ξ x))
    simpa using h3

/-- For `m ∈ S^{-s}`, `s > 0`, the multiplier is convolution with the integrable kernel
`negKernel m`, for every Schwartz function. -/
theorem vecMultiplier_eq_negKernel {s : ℝ} (hs : 0 < s) {m : Vec d → ℂ} (hm : IsSymbol (-s) m)
    (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    vecMultiplier m f x = ∫ y, negKernel m (x - y) * f y := by
  set M : ℝ := SchwartzMap.seminorm ℝ 0 0 f with hM
  have hfb : ∀ y, ‖f y‖ ≤ M := fun y => by
    simpa using SchwartzMap.le_seminorm ℝ 0 0 f y
  have hint : ∀ l, Integrable (fun y => lpKernel m l (x - y) * f y) := fun l => by
    exact ((integrable_lpKernel hm.1 l).comp_sub_left x).mul_bdd (c := M)
      f.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  have hsum : Summable fun l => ∫ y, ‖lpKernel m l (x - y) * f y‖ := by
    refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun y => norm_nonneg _)
      (fun l => ?_) ((summable_integral_norm_lpKernel hs hm).mul_left M)
    calc ∫ y, ‖lpKernel m l (x - y) * f y‖ ≤ ∫ y, M * ‖lpKernel m l (x - y)‖ := by
          refine integral_mono (hint l).norm
            (((integrable_lpKernel hm.1 l).comp_sub_left x).norm.const_mul M) fun y => ?_
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hfb y) (norm_nonneg _)
      _ = M * ∫ y, ‖lpKernel m l y‖ := by
          rw [integral_const_mul]
          congr 1
          exact integral_sub_left_eq_self (fun y => ‖lpKernel m l y‖) volume x
  have h1 := hasSum_integral_of_summable_integral_norm hint hsum
  have h2 : ∫ y, (∑' l, lpKernel m l (x - y) * f y) = ∫ y, negKernel m (x - y) * f y := by
    congr 1; funext y; rw [tsum_mul_right]; rfl
  rw [h2] at h1
  have h3 : Tendsto (fun L => ∑ l ∈ Finset.range (L + 1), vecMultiplier (lpSym m l) f x) atTop
      (𝓝 (∫ y, negKernel m (x - y) * f y)) := by
    simp_rw [vecMultiplier_lpSym hm.1]
    exact (h1.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  exact tendsto_nhds_unique (tendsto_sum_vecMultiplier_lpSym hm.hasTemperateGrowth f x) h3

end

end AFree
