module

public import AFree.TopCurrents.Piola
public import AFree.TopCurrents.WStarMinor
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration by parts for minors of Lipschitz maps
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace AFree

open PDE

variable {d m s : ℕ}

private lemma contDiff_entry {G : Vec d → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (w : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ G y w) :=
  ((hG.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const)

private lemma contDiff_minorDet (G : Fin m → Vec d → ℝ) (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i))
    (r : Fin s → Fin m) (c : Fin s → Fin d) : ContDiff ℝ (⊤ : ℕ∞) (minorDet G r c) := by
  have e : minorDet G r c = fun y => ∑ σ : Equiv.Perm (Fin s), Equiv.Perm.sign σ •
      ∏ i, fderiv ℝ (G (r (σ i))) y (Pi.single (c i) 1) := by
    funext y
    simp [minorDet, jacMat, Matrix.det_apply]
  rw [e]
  refine ContDiff.sum fun σ _ => ContDiff.const_smul _ ?_
  exact contDiff_prod fun i _ => contDiff_entry (hG _) _

/-- Integration by parts for a smooth tuple. -/
private theorem ibp_smooth (G : Fin m → Vec d → ℝ) (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (r : Fin (s + 1) → Fin m) (c : Fin (s + 1) → Fin d) :
    ∫ x, φ x * minorDet G r c x = -∑ b : Fin (s + 1), (-1) ^ (b : ℕ) *
      ∫ x, fderiv ℝ φ x (Pi.single (c b) 1) *
        (G (r 0) x * minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) x) := by
  have hG2 : ∀ i, ContDiff ℝ 2 (G i) := fun i => (hG i).of_le (by norm_num)
  set Q : Fin (s + 1) → Vec d → ℝ := fun b y =>
    G (r 0) y * minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y with hQ
  have hQs : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (Q b) := fun b =>
    (hG (r 0)).mul (contDiff_minorDet G hG _ _)
  have hQ1 : ∀ b, ContDiff ℝ 1 (Q b) := fun b => (hQs b).of_le (by exact_mod_cast le_top)
  have h1 : ∀ x, φ x * minorDet G r c x = ∑ b : Fin (s + 1), (-1) ^ (b : ℕ) *
      (φ x * fderiv ℝ (Q b) x (Pi.single (c b) 1)) := by
    intro x
    rw [(piola G hG2 r c x).2.2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [h1]
  have hint : ∀ b, Integrable (fun x => φ x * fderiv ℝ (Q b) x (Pi.single (c b) 1)) volume := by
    intro b
    refine Continuous.integrable_of_hasCompactSupport ?_ hφc.mul_right
    exact hφ.continuous.mul (((hQ1 b).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  rw [integral_finsetSum _ fun b _ => (hint b).const_mul _, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, neg_mul_eq_mul_neg]
  congr 1
  have hQd : ∀ x, DifferentiableAt ℝ (Q b) x := fun x => (hQ1 b).differentiable one_ne_zero x
  have hφd : ∀ x, DifferentiableAt ℝ φ x := fun x => hφ.differentiable one_ne_zero x
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := φ)
    (g := Q b) (v := Pi.single (c b) 1) ?_ ?_ ?_ (fun x _ => hφd x) (fun x _ => hQd x)
  · simpa [hQ] using hIBP
  · refine Continuous.integrable_of_hasCompactSupport ?_ (hφc.fderiv_apply ℝ _ |>.mul_right)
    exact ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul (hQs b).continuous
  · exact hint b
  · exact Continuous.integrable_of_hasCompactSupport (hφ.continuous.mul (hQs b).continuous)
      hφc.mul_right

private theorem tendsto_int_minor {C : ℝ≥0} {Gn : ℕ → Fin m → Vec d → ℝ} {F : Fin m → Vec d → ℝ}
    (hGn : ∀ n i, IsEuclLipschitzWith C (Gn n i)) {r' : Fin s → Fin m} {c' : Fin s → Fin d}
    (hc : Function.Injective c')
    (hconv : ∀ᵐ x, Tendsto (fun n => minorDet (Gn n) r' c' x) atTop (𝓝 (minorDet F r' c' x)))
    {θ : ℕ → Vec d → ℝ} {θ' : Vec d → ℝ} (hθm : ∀ n, Measurable (θ n))
    (hθl : ∀ x, Tendsto (fun n => θ n x) atTop (𝓝 (θ' x))) {B : Vec d → ℝ}
    (hB : Integrable B volume) (hdom : ∀ n x, |θ n x| ≤ B x) :
    Tendsto (fun n => ∫ x, θ n x * minorDet (Gn n) r' c' x) atTop
      (𝓝 (∫ x, θ' x * minorDet F r' c' x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => B x * (C : ℝ) ^ s)
    (fun n => ((hθm n).mul (minorDet_measurable _ _ _)).aestronglyMeasurable)
    (hB.mul_const _) ?_ ?_
  · intro n
    filter_upwards [ae_abs_minorDet_le (hGn n) r' c' hc] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hdom n x) hx (abs_nonneg _) ((abs_nonneg _).trans (hdom n x))
  · filter_upwards [hconv] with x hx using (hθl x).mul hx

/-- Integration by parts for the minors of a Euclidean-Lipschitz tuple:
`∫ φ M_{I,J}(F) = -∑_b (-1)^{b+1} ∫ ∂_{j_b} φ F_{i_1} M_{I',J^b}(F)` for `φ ∈ C¹_c`. -/
theorem ibpminor {C : ℝ≥0} {F : Fin m → Vec d → ℝ} (hF : ∀ i, IsEuclLipschitzWith C (F i))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (r : Fin (s + 1) → Fin m)
    (c : Fin (s + 1) → Fin d) (hc : Function.Injective c) :
    ∫ x, φ x * minorDet F r c x = -∑ b : Fin (s + 1), (-1) ^ (b : ℕ) *
      ∫ x, fderiv ℝ φ x (Pi.single (c b) 1) * F (r 0) x *
        minorDet F (r ∘ Fin.succ) (c ∘ b.succAbove) x := by
  set Gn : ℕ → Fin m → Vec d → ℝ := fun n i =>
    mollLip (stdMollifier d) (1 / ((n : ℝ) + 1)) (F i) with hGn
  have hρ := isMollifierKernel_stdMollifier d
  obtain ⟨hunif, hsm, -, hconvM, -⟩ := mollmap hρ (K := fun _ => C) hF
  have hLip : ∀ n i, IsEuclLipschitzWith C (Gn n i) := fun n i => (hsm i n).2
  have hSm : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (Gn n i) := fun n i => (hsm i n).1
  have hpt : ∀ i x, Tendsto (fun n => Gn n i x) atTop (𝓝 (F i x)) :=
    fun i x => (hunif i).tendsto_at x
  have hIBP : ∀ n, ∫ x, φ x * minorDet (Gn n) r c x = -∑ b : Fin (s + 1), (-1) ^ (b : ℕ) *
      ∫ x, (fderiv ℝ φ x (Pi.single (c b) 1) * Gn n (r 0) x) *
        minorDet (Gn n) (r ∘ Fin.succ) (c ∘ b.succAbove) x := by
    intro n
    rw [ibp_smooth (Gn n) (hSm n) hφ hφc r c]
    simp only [mul_assoc]
  have hφm : Measurable φ := hφ.continuous.measurable
  have hLHS : Tendsto (fun n => ∫ x, φ x * minorDet (Gn n) r c x) atTop
      (𝓝 (∫ x, φ x * minorDet F r c x)) :=
    tendsto_int_minor hLip hc (hconvM (s + 1) r c hc) (θ := fun _ => φ) (fun _ => hφm)
      (fun _ => tendsto_const_nhds)
      (hφ.continuous.integrable_of_hasCompactSupport hφc).abs (fun _ x => le_rfl)
  have hRHS : ∀ b : Fin (s + 1), Tendsto (fun n => ∫ x, (fderiv ℝ φ x (Pi.single (c b) 1) *
      Gn n (r 0) x) * minorDet (Gn n) (r ∘ Fin.succ) (c ∘ b.succAbove) x) atTop
      (𝓝 (∫ x, (fderiv ℝ φ x (Pi.single (c b) 1) * F (r 0) x) *
        minorDet F (r ∘ Fin.succ) (c ∘ b.succAbove) x)) := by
    intro b
    have hcb : Function.Injective (c ∘ b.succAbove) := hc.comp (Fin.succAbove_right_injective)
    have hdφ : Continuous fun x => fderiv ℝ φ x (Pi.single (c b) 1) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hFc : Continuous (F (r 0)) := MetricCurrents.Moll.continuous_of_eucl (hF _)
    have hmeas : ∀ n, Measurable fun x => fderiv ℝ φ x (Pi.single (c b) 1) * Gn n (r 0) x :=
      fun n => hdφ.measurable.mul ((hSm n (r 0)).continuous.measurable)
    refine tendsto_int_minor hLip hcb (hconvM s (r ∘ Fin.succ) (c ∘ b.succAbove) hcb) hmeas
      (fun x => tendsto_const_nhds.mul (hpt _ x))
      (B := fun x => |fderiv ℝ φ x (Pi.single (c b) 1)| * (|F (r 0) x| + Real.sqrt d * C)) ?_ ?_
    · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact hdφ.abs.mul (hFc.abs.add continuous_const)
      · exact HasCompactSupport.mul_right (by
          simpa using (hφc.fderiv_apply ℝ (Pi.single (c b) (1 : ℝ) : Vec d)).norm)
    · intro n x
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have h1 := (mollLip_smooth_lipschitz hρ (hF (r 0)) hε).2.2 x
      have hε1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h2 : Real.sqrt d * C * (1 / ((n : ℝ) + 1)) ≤ Real.sqrt d * C :=
        mul_le_of_le_one_right (by positivity) hε1
      have h3 : |Gn n (r 0) x - F (r 0) x| ≤ Real.sqrt d * C := h1.trans h2
      calc |Gn n (r 0) x| = |F (r 0) x + (Gn n (r 0) x - F (r 0) x)| := by ring_nf
        _ ≤ |F (r 0) x| + |Gn n (r 0) x - F (r 0) x| := abs_add_le _ _
        _ ≤ _ := by linarith
  have hlim2 := (tendsto_finsetSum Finset.univ fun b _ => (hRHS b).const_mul ((-1 : ℝ) ^ (b : ℕ))).neg
  exact tendsto_nhds_unique (hLHS.congr hIBP) hlim2

end AFree
