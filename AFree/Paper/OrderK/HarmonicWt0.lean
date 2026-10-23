module

public import AFree.Paper.OrderK.HarmonicDual
public import AFree.Harmonic.Kernel
public import AFree.Harmonic.WeakTypeKernel

/-!
# Weak type `(1,1)` of an order-`0` multiplier

Reality of `T_m f` and the weak type estimate,
by the limit step `K_L ⋆ f → T_m f` and Fatou for sets.
-/

@[expose] public section

open MeasureTheory PDE Filter Topology
open scoped SchwartzMap ComplexConjugate

namespace AFree

noncomputable section

variable {d : ℕ}

theorem conj_fourierChar_smul' (t : ℝ) (z : ℂ) :
    conj (Real.fourierChar t • z) = Real.fourierChar (-t) • conj z := by
  have h : conj ((Real.fourierChar t : Circle) : ℂ) = ((Real.fourierChar (-t) : Circle) : ℂ) := by
    rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  simp only [Circle.smul_def, smul_eq_mul, map_mul, h]

theorem conj_vecFourier_of_real (f : Vec d → ℝ) (ξ : Vec d) :
    conj (vecFourier (fun y => (f y : ℂ)) ξ) = vecFourier (fun y => (f y : ℂ)) (-ξ) := by
  rw [vecFourier_neg_eq, vecFourier_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [conj_fourierChar_smul']
  simp [vecDot, mul_comm]

/-- Reality of `T_m f` for real `f ∈ C_c^∞` and `m(-ξ) = conj m(ξ)`. -/
theorem im_ccMult_eq_zero {m : Vec d → ℂ} (hm : IsSymbol 0 m)
    (hreal : ∀ ξ, m (-ξ) = conj (m ξ)) {f : Vec d → ℝ} (hf : IsCc f) (x : Vec d) :
    (ccMult m f x).im = 0 := by
  have hT := hm.hasTemperateGrowth
  have hfc : (fun y => (f y : ℂ)) = ⇑(schw f) := funext fun y => (schw_apply hf y).symm
  have key : conj (ccMult m f x) = ccMult m f x := by
    unfold ccMult
    rw [vecMultiplier_apply_integral hT, ← integral_conj]
    rw [← integral_neg_eq_self (fun ξ => Real.fourierChar (vecDot ξ x) •
      (m ξ * vecFourier (schw f) ξ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [conj_fourierChar_smul', map_mul, ← hreal, ← hfc, conj_vecFourier_of_real]
    have : vecDot (-ξ) x = -vecDot ξ x := by unfold vecDot; simp
    rw [this]
  have := congrArg Complex.im key
  simp only [Complex.conj_im] at this
  linarith

theorem hasCompactSupport_of_tsupport_subset_ball' {f : Vec d → ℝ}
    (hf : tsupport f ⊆ euclideanBall (0 : Vec d) 1) : HasCompactSupport f :=
  (isCompact_euclideanClosedBall (0 : Vec d) zero_le_one).of_isClosed_subset (isClosed_tsupport _)
    (hf.trans (euclideanBall_subset_euclideanClosedBall _ _))

/-- The weak type estimate (ii) of `lem_wt0`. -/
theorem weakType_ccMult {m : Vec d → ℂ} (hd : 0 < d) (hm : IsSymbol 0 m)
    (hreal : ∀ ξ, m (-ξ) = conj (m ξ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      tsupport f ⊆ euclideanBall (0 : Vec d) 1 → ∀ lam : ℝ, 0 < lam →
        volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < ‖ccMult m f x‖} ≤
          ENNReal.ofReal (C / lam * ∫ x, |f x|) := by
  obtain ⟨Cd, hCd, hW⟩ := exists_weakTypeOne_of_hormander hd
  obtain ⟨A, hA0, -, hK⟩ := exists_uniform_hormander_kernels hm hreal
  refine ⟨Cd * A + 1, by positivity, fun f hf hfs lam hlam => ?_⟩
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_ball' hfs
  have hfI : IsCc f := ⟨hf, hfc⟩
  set I : ℝ := ∫ x, |f x| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  -- bound for each truncation
  have hbound : ∀ L : ℕ, ∀ l : ℝ, 0 < l → volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
      l < |∫ y, realKernel m L (x - y) * f y|} ≤ ENNReal.ofReal (Cd * A / l * I) := fun L l hl =>
    hW (realKernel m L) A (hK L).1 (hK L).2.1 hA0 (hK L).2.2.1 (hK L).2.2.2 f hf hfs l hl
  have hconv : ∀ x, Tendsto (fun L => ((∫ y, realKernel m L (x - y) * f y : ℝ) : ℂ)) atTop
      (𝓝 (ccMult m f x)) := by
    intro x
    have := tendsto_realKernel_conv hm hreal (schw f) x
    refine this.congr fun L => ?_
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [schw_apply hfI]
  have hlim : ∀ l : ℝ, 0 < l → l < lam →
      volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < ‖ccMult m f x‖} ≤
        ENNReal.ofReal (Cd * A / l * I) := by
    intro l hl hll
    set E : ℕ → Set (Vec d) := fun N => {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
      ∀ L, N ≤ L → l < |∫ y, realKernel m L (x - y) * f y|} with hE
    have hmono : Monotone E := fun N N' h x hx => ⟨hx.1, fun L hL => hx.2 L (h.trans hL)⟩
    have hsub : {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < ‖ccMult m f x‖} ⊆ ⋃ N, E N := by
      rintro x ⟨hx2, hx⟩
      have h1 := ((continuous_norm.tendsto _).comp (hconv x)).eventually (lt_mem_nhds hx)
      obtain ⟨N, hN⟩ := eventually_atTop.1 h1
      refine Set.mem_iUnion.2 ⟨N, hx2, fun L hL => ?_⟩
      have := hN L hL
      simp only [Function.comp, Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    calc volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < ‖ccMult m f x‖}
        ≤ volume (⋃ N, E N) := measure_mono hsub
      _ = ⨆ N, volume (E N) := hmono.measure_iUnion
      _ ≤ _ := iSup_le fun N => (measure_mono fun x (hx : x ∈ E N) => (⟨hx.1, hx.2 N le_rfl⟩ :
              x ∈ euclideanBall (0 : Vec d) 2 ∧ l < |∫ y, realKernel m N (x - y) * f y|)).trans
            (hbound N l hl)
  -- let `l ↑ lam`
  have hev : ∀ᶠ l in 𝓝[<] lam, volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
      lam < ‖ccMult m f x‖} ≤ ENNReal.ofReal (Cd * A / l * I) := by
    filter_upwards [Ioo_mem_nhdsLT hlam] with l hl using hlim l hl.1 hl.2
  have hcont : Tendsto (fun l : ℝ => ENNReal.ofReal (Cd * A / l * I)) (𝓝[<] lam)
      (𝓝 (ENNReal.ofReal (Cd * A / lam * I))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have : ContinuousAt (fun l : ℝ => Cd * A / l * I) lam :=
      ((continuousAt_const.div continuousAt_id hlam.ne').mul continuousAt_const)
    exact this.tendsto
  have := ge_of_tendsto hcont hev
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  have : Cd * A / lam * I ≤ (Cd * A + 1) / lam * I :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hlam.le) hI0
  exact this

/-- Weak type `(1,1)` of an order-`0` multiplier: for `m ∈ S⁰` with
`m(-ξ) = conj m(ξ)` there is `C_m > 0` such that (i) `T_m f` is real for real `f ∈ C_c^∞` and
(ii) `|{x ∈ B₂ : |T_m f x| > λ}| ≤ C_m λ⁻¹ ‖f‖₁` for real `f ∈ C^∞` with `tsupp f ⊆ B₁`. -/
theorem lem_wt0 {m : Vec d → ℂ} (hd : 0 < d) (hm : IsSymbol 0 m)
    (hreal : ∀ ξ, m (-ξ) = conj (m ξ)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ f : Vec d → ℝ, IsCc f → ∀ x, (ccMult m f x).im = 0) ∧
      ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → tsupport f ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam →
          volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧ lam < ‖ccMult m f x‖} ≤
            ENNReal.ofReal (C / lam * ∫ x, |f x|) := by
  obtain ⟨C, hC, h⟩ := weakType_ccMult hd hm hreal
  exact ⟨C, hC, fun f hf x => im_ccMult_eq_zero hm hreal hf x, h⟩

end

end AFree
