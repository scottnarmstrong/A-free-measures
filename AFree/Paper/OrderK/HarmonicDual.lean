module

public import AFree.Paper.OrderK.HarmonicBasic

/-!
# Duality and `L^∞` bound for bounded even multipliers

For a bounded even multiplier, `T_m` is self-adjoint on real `C_c^∞` functions and bounded by `‖ψ̂‖₁`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap

namespace AFree

noncomputable section

variable {d : ℕ}

theorem continuous_vecDot_pair : Continuous fun p : Vec d × Vec d => vecDot p.1 p.2 := by
  unfold vecDot
  fun_prop

theorem vecFourier_neg_eq (f : Vec d → ℂ) (ξ : Vec d) :
    vecFourier f (-ξ) = ∫ x, Real.fourierChar (vecDot ξ x) • f x := by
  rw [vecFourier_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have : vecDot x (-ξ) = -vecDot ξ x := by
    rw [vecDot_comm]; unfold vecDot; simp
  simp [this]

theorem integrable_norm_vecFourier (f : 𝓢(Vec d, ℂ)) : Integrable fun ξ => ‖vecFourier f ξ‖ := by
  rw [← vecFourier_coe]; exact (vecFourierCLM f).integrable.norm

theorem continuous_vecFourier' (f : 𝓢(Vec d, ℂ)) : Continuous (vecFourier f) := by
  rw [← vecFourier_coe]; exact (vecFourierCLM f).continuous

/-- Fubini: `∫ φ · T_m g = ∫ φ̂(-ξ) m(ξ) ĝ(ξ) dξ`. -/
theorem integral_mul_vecMultiplier {m : Vec d → ℂ} (hm : IsSymbol 0 m) {A : ℝ}
    (hA : ∀ ξ, ‖m ξ‖ ≤ A) (φ g : 𝓢(Vec d, ℂ)) :
    ∫ x, φ x * vecMultiplier m g x = ∫ ξ, vecFourier φ (-ξ) * (m ξ * vecFourier g ξ) := by
  have hT := hm.hasTemperateGrowth
  simp_rw [vecMultiplier_apply_integral hT]
  set F : Vec d → Vec d → ℂ := fun x ξ =>
    φ x * (Real.fourierChar (vecDot ξ x) • (m ξ * vecFourier g ξ)) with hF
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hb : Integrable (fun p : Vec d × Vec d => ‖φ p.1‖ * (A * ‖vecFourier g p.2‖))
        (volume.prod volume) :=
      φ.integrable.norm.mul_prod ((integrable_norm_vecFourier g).const_mul A)
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have hc : Continuous (Function.uncurry F) := by
        have h1 : Continuous fun p : Vec d × Vec d =>
            Real.fourierChar (vecDot p.2 p.1) :=
          Real.continuous_fourierChar.comp (continuous_vecDot_pair.comp continuous_swap)
        have h2 : Continuous fun p : Vec d × Vec d => vecFourier g p.2 :=
          (continuous_vecFourier' g).comp continuous_snd
        have h3 : Continuous fun p : Vec d × Vec d => m p.2 := hm.1.continuous.comp continuous_snd
        have h4 : Continuous fun p : Vec d × Vec d => φ p.1 := φ.continuous.comp continuous_fst
        change Continuous fun p : Vec d × Vec d =>
          φ p.1 * (Real.fourierChar (vecDot p.2 p.1) • (m p.2 * vecFourier g p.2))
        refine h4.mul ?_
        exact h1.smul (h3.mul h2)
      exact hc.aestronglyMeasurable
    · simp only [Function.uncurry, hF, norm_mul, Circle.norm_smul, norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _))
        (norm_nonneg _)
  have hsw := integral_integral_swap (f := F) hint
  have e1 : ∀ x, φ x * ∫ ξ, Real.fourierChar (vecDot ξ x) • (m ξ * vecFourier g ξ) =
      ∫ ξ, F x ξ := fun x => by
    rw [hF, integral_const_mul]
  simp_rw [e1]
  rw [hsw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [vecFourier_neg_eq]
  simp only [hF]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- `‖T_m φ‖_∞ ≤ A ‖φ̂‖₁`. -/
theorem norm_vecMultiplier_le {m : Vec d → ℂ} (hm : IsSymbol 0 m) {A : ℝ}
    (hA : ∀ ξ, ‖m ξ‖ ≤ A) (φ : 𝓢(Vec d, ℂ)) (x : Vec d) :
    ‖vecMultiplier m φ x‖ ≤ A * ∫ ξ, ‖vecFourier φ ξ‖ := by
  rw [vecMultiplier_apply_integral hm.hasTemperateGrowth, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_norm_vecFourier φ).const_mul A)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Circle.norm_smul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hA ξ) (norm_nonneg _)

/-- Duality and `L^∞` bound for bounded even multipliers: for `m ∈ S⁰` even with
`|m| ≤ A` and real `ψ, G ∈ C_c^∞`, `∫ ψ T_m G = ∫ G T_m ψ`, `‖T_m ψ‖_∞ ≤ A ‖ψ̂‖₁`, hence
`|∫ ψ T_m G| ≤ A ‖ψ̂‖₁ ‖G‖₁`. -/
theorem lem_dual {m : Vec d → ℂ} (hm : IsSymbol 0 m) (heven : ∀ ξ, m (-ξ) = m ξ) {A : ℝ}
    (hA : ∀ ξ, ‖m ξ‖ ≤ A) {ψ G : Vec d → ℝ} (hψ : IsCc ψ) (hG : IsCc G) :
    (∫ x, (ψ x : ℂ) * ccMult m G x = ∫ x, (G x : ℂ) * ccMult m ψ x) ∧
    (∀ x, ‖ccMult m ψ x‖ ≤ A * ∫ ξ, ‖vecFourier (fun y => (ψ y : ℂ)) ξ‖) ∧
    ‖∫ x, (ψ x : ℂ) * ccMult m G x‖ ≤
      A * (∫ ξ, ‖vecFourier (fun y => (ψ y : ℂ)) ξ‖) * ∫ x, |G x| := by
  have hψf : (fun y => (ψ y : ℂ)) = ⇑(schw ψ) := funext fun y => (schw_apply hψ y).symm
  have hGf : (fun y => (G y : ℂ)) = ⇑(schw G) := funext fun y => (schw_apply hG y).symm
  have hdual : ∫ x, (ψ x : ℂ) * ccMult m G x = ∫ x, (G x : ℂ) * ccMult m ψ x := by
    have e1 : ∫ x, (ψ x : ℂ) * ccMult m G x =
        ∫ ξ, vecFourier (schw ψ) (-ξ) * (m ξ * vecFourier (schw G) ξ) := by
      rw [← integral_mul_vecMultiplier hm hA]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [ccMult, schw_apply hψ])
    have e2 : ∫ x, (G x : ℂ) * ccMult m ψ x =
        ∫ ξ, vecFourier (schw G) (-ξ) * (m ξ * vecFourier (schw ψ) ξ) := by
      rw [← integral_mul_vecMultiplier hm hA]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [ccMult, schw_apply hG])
    rw [e1, e2, ← integral_neg_eq_self (fun ξ =>
      vecFourier (schw G) (-ξ) * (m ξ * vecFourier (schw ψ) ξ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [neg_neg, heven]
    ring
  have hbd : ∀ x, ‖ccMult m ψ x‖ ≤ A * ∫ ξ, ‖vecFourier (fun y => (ψ y : ℂ)) ξ‖ := fun x => by
    rw [hψf]; exact norm_vecMultiplier_le hm hA _ x
  refine ⟨hdual, hbd, ?_⟩
  rw [hdual]
  have hGi : Integrable fun x => |G x| := by
    have : Integrable G := hG.1.continuous.integrable_of_hasCompactSupport hG.2
    simpa using this.norm
  have hm' : ∀ x, ‖(G x : ℂ) * ccMult m ψ x‖ ≤
      |G x| * (A * ∫ ξ, ‖vecFourier (fun y => (ψ y : ℂ)) ξ‖) := fun x => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbd x) (abs_nonneg _)
  calc ‖∫ x, (G x : ℂ) * ccMult m ψ x‖
      ≤ ∫ x, |G x| * (A * ∫ ξ, ‖vecFourier (fun y => (ψ y : ℂ)) ξ‖) :=
        norm_integral_le_of_norm_le (hGi.mul_const _) (Filter.Eventually.of_forall hm')
    _ = _ := by rw [integral_mul_const]; ring

end

end AFree
