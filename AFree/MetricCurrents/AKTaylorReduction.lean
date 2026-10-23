module

public import AFree.MetricCurrents.AKTaylorBasic
public import AFree.MetricCurrents.LipApprox

/-!
# Taylor lemma, Step 0: reduction to cut-off Lipschitz weights
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKTaylor

open PDE AFree

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ} {π : Fin k → Vec d → ℝ}
  {ψ : Fin k → Vec k → ℝ} {Λ M : ℝ≥0} {μ : Measure (Vec d)}

/-- The Lipschitz cut-off `θ_R(y) = min(1, max(0, R + 1 - ‖y‖))` (sup norm). -/
noncomputable def theta (R : ℝ) (y : Vec k) : ℝ := min 1 (max 0 (R + 1 - ‖y‖))

lemma theta_nonneg (R : ℝ) (y : Vec k) : 0 ≤ theta R y := by
  unfold theta; exact le_min zero_le_one (le_max_left _ _)

lemma theta_le_one (R : ℝ) (y : Vec k) : theta R y ≤ 1 := min_le_left _ _

lemma theta_eq_one {R : ℝ} {y : Vec k} (h : ‖y‖ ≤ R) : theta R y = 1 := by
  unfold theta
  rw [min_eq_left]
  exact le_max_of_le_right (by linarith)

lemma theta_eq_zero {R : ℝ} {y : Vec k} (h : R + 1 ≤ ‖y‖) : theta R y = 0 := by
  unfold theta
  rw [max_eq_left (by linarith)]; exact min_eq_right zero_le_one

lemma ne_zero_imp_norm_lt {R : ℝ} {y : Vec k} (h : theta R y ≠ 0) : ‖y‖ < R + 1 := by
  by_contra hc
  exact h (theta_eq_zero (not_lt.1 hc))

lemma abs_theta_sub_le (R : ℝ) (y y' : Vec k) : |theta R y - theta R y'| ≤ 1 * ‖y - y'‖ := by
  have h1 : |‖y‖ - ‖y'‖| ≤ ‖y - y'‖ := abs_norm_sub_norm_le _ _
  have h2 : |max 0 (R + 1 - ‖y‖) - max 0 (R + 1 - ‖y'‖)| ≤ ‖y - y'‖ := by
    rw [max_comm 0, max_comm 0 (R + 1 - ‖y'‖)]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rwa [show R + 1 - ‖y‖ - (R + 1 - ‖y'‖) = -(‖y‖ - ‖y'‖) by ring, abs_neg]
  have h3 := abs_min_sub_min_le_max (1 : ℝ) (max 0 (R + 1 - ‖y‖)) (1 : ℝ) (max 0 (R + 1 - ‖y'‖))
  rw [one_mul]
  unfold theta
  refine h3.trans (max_le (by simp) h2)

/-- The cut-off weight `f_R = f · θ_R ∘ π`. -/
noncomputable def cutoffWeight (π : Fin k → Vec d → ℝ) (R : ℝ) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  f x * theta R (evalTuple π x)

lemma lipb_cutoffWeight (c : Ctx T π ψ Λ M μ) (R : ℝ) {f : Vec d → ℝ} (hf : IsBddLipFun f) :
    IsBddLipFun (cutoffWeight π R f) := by
  refine lipb_mul hf ⟨⟨_, lip_comp c.hπ (theta R) 1 (abs_theta_sub_le R)⟩, 1, fun x => ?_⟩
  rw [abs_of_nonneg (theta_nonneg _ _)]; exact theta_le_one _ _

/-- The difference of the two sides of the Taylor identity. -/
noncomputable def Dfun (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ) (π : Fin k → Vec d → ℝ)
    (ψ : Fin k → Vec k → ℝ) (h : Vec d → ℝ) : ℝ :=
  akExt T h (psiPi ψ π) - akExt T (jacW ψ π h) π

lemma Dfun_sub (c : Ctx T π ψ Λ M μ) {h g : Vec d → ℝ} (hh : IsBorelBdd h) (hg : IsBorelBdd g) :
    Dfun T π ψ (fun x => h x - g x) = Dfun T π ψ h - Dfun T π ψ g := by
  have E := (akext c.hT).1.2.1
  have e1 : (fun x => h x - g x) = (1 : ℝ) • h + (-1 : ℝ) • g := by funext x; simp; ring
  have e2 : jacW ψ π (fun x => h x - g x) = (1 : ℝ) • jacW ψ π h + (-1 : ℝ) • jacW ψ π g := by
    funext x; simp only [jacW, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  unfold Dfun
  rw [e2, E π c.isLipTuple _ _ (borelBdd_mul_jacDet c hh) (borelBdd_mul_jacDet c hg), e1,
    E _ (isLipTuple_psi c) _ _ hh hg]
  ring

lemma abs_Dfun_le (c : Ctx T π ψ Λ M μ) {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    |Dfun T π ψ h| ≤ ((M * Λ : ℝ) ^ k + (Λ : ℝ) ^ k * (Real.sqrt k * M) ^ k) * ∫ x, |h x| ∂μ := by
  have := c.hμ.1.1
  have h1 := abs_akExt_le c hh (π' := psiPi ψ π) (K := fun _ => M * Λ)
    (fun i => lip_comp c.hπ (ψ i) M (psi_lip c i))
  have h2 := abs_akExt_le c (borelBdd_mul_jacDet c hh) (π' := π) (K := fun _ => Λ) c.hπ
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, NNReal.coe_mul] at h1 h2
  have hint : ∫ x, |jacW ψ π h x| ∂μ ≤ (Real.sqrt k * M) ^ k * ∫ x, |h x| ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
      ((integrable_of_borelBdd hh).abs.const_mul _) (Eventually.of_forall fun x => ?_)
    simp only [jacW, abs_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_jacDet_le c _) (abs_nonneg _)
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) ^ k := pow_nonneg Λ.coe_nonneg _
  unfold Dfun
  refine (abs_sub _ _).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hint hΛ]

lemma eq_zero_of_bound {a : ℝ} {u : ℕ → ℝ} (h : ∀ n, |a| ≤ u n) (hu : Tendsto u atTop (𝓝 0)) :
    a = 0 := by
  have := ge_of_tendsto' hu h
  exact abs_nonpos_iff.1 this

/-- Step 0. By linearity (E2) and the mass bound (E4) of the extension,
it suffices to prove the identity for the cut-off weights `f_R = f · θ_R ∘ π`, `f ∈ Lip_b`, `R > 0`. -/
theorem reduction (c : Ctx T π ψ Λ M μ)
    (hfR : ∀ f, IsBddLipFun f → ∀ R : ℝ, 0 < R → Dfun T π ψ (cutoffWeight π R f) = 0) :
    ∀ h, IsBorelBdd h → Dfun T π ψ h = 0 := by
  have := c.hμ.1.1
  set C₀ : ℝ := (M * Λ : ℝ) ^ k + (Λ : ℝ) ^ k * (Real.sqrt k * M) ^ k
  -- Step A: Lipschitz weights
  have hlip : ∀ f, IsBddLipFun f → Dfun T π ψ f = 0 := by
    intro f hf
    have hfb := borelBdd_of_lipb hf
    have hRb : ∀ n : ℕ, IsBorelBdd (cutoffWeight π ((n : ℝ) + 1) f) := fun n =>
      borelBdd_of_lipb (lipb_cutoffWeight c _ hf)
    have hsub : ∀ n : ℕ, Dfun T π ψ f =
        Dfun T π ψ (fun x => f x - cutoffWeight π ((n : ℝ) + 1) f x) := by
      intro n
      rw [Dfun_sub c hfb (hRb n), hfR f hf _ (by positivity)]; ring
    refine eq_zero_of_bound (u := fun n : ℕ =>
      C₀ * ∫ x, |f x - cutoffWeight π ((n : ℝ) + 1) f x| ∂μ) (fun n => ?_) ?_
    · rw [hsub n]
      exact abs_Dfun_le c ⟨(hfb.1.sub (hRb n).1), by
        obtain ⟨C, hC⟩ := hfb.2
        obtain ⟨C', hC'⟩ := (hRb n).2
        exact ⟨C + C', fun x => (abs_sub _ _).trans (add_le_add (hC x) (hC' x))⟩⟩
    · rw [show (0 : ℝ) = C₀ * 0 by ring]
      refine Tendsto.const_mul _ ?_
      have : Tendsto (fun n : ℕ => ∫ x, |f x - cutoffWeight π ((n : ℝ) + 1) f x| ∂μ) atTop
          (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
        refine tendsto_integral_of_dominated_convergence (fun x => |f x|) (fun n => ?_)
          ((integrable_of_borelBdd hfb).abs) (fun n => Eventually.of_forall fun x => ?_)
          (Eventually.of_forall fun x => ?_)
        · exact ((hfb.1.sub (hRb n).1).norm).aestronglyMeasurable
        · have h0 := theta_nonneg ((n : ℝ) + 1) (evalTuple π x)
          have h1 := theta_le_one ((n : ℝ) + 1) (evalTuple π x)
          simp only [cutoffWeight, Real.norm_eq_abs]
          rw [abs_abs, ← mul_one_sub, abs_mul, abs_of_nonneg (sub_nonneg.2 h1)]
          nlinarith [abs_nonneg (f x)]
        · refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖evalTuple π x‖⌉₊) fun n hn => ?_
          have : ‖evalTuple π x‖ ≤ (n : ℝ) + 1 :=
            (Nat.le_ceil _).trans ((Nat.cast_le.2 hn).trans (by linarith))
          simp [cutoffWeight, theta_eq_one this]
      simpa using this
  -- Step B: Borel weights
  intro h hh
  have : IsFiniteMeasure μ := c.hμ.1.1
  obtain ⟨g, hg, hglim⟩ := exists_lip_approx_borelBdd μ hh
  have hgb := fun n => borelBdd_of_lipb (hg n)
  refine eq_zero_of_bound (u := fun n => C₀ * ∫ x, |g n x - h x| ∂μ) (fun n => ?_) ?_
  · have hsub : Dfun T π ψ h = Dfun T π ψ (fun x => h x - g n x) := by
      rw [Dfun_sub c hh (hgb n), hlip _ (hg n)]; ring
    rw [hsub]
    have hbb : IsBorelBdd (fun x => h x - g n x) := by
      refine ⟨hh.1.sub (hgb n).1, ?_⟩
      obtain ⟨C, hC⟩ := hh.2
      obtain ⟨C', hC'⟩ := (hgb n).2
      exact ⟨C + C', fun x => (abs_sub _ _).trans (add_le_add (hC x) (hC' x))⟩
    refine (abs_Dfun_le c hbb).trans (le_of_eq ?_)
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact abs_sub_comm _ _
  · rw [show (0 : ℝ) = C₀ * 0 by ring]
    exact hglim.const_mul _

end AFree.MetricCurrents.AKTaylor
