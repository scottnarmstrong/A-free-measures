module

public import AFree.MetricCurrents.AKTaylorSummation

/-!
# Taylor lemma, Step 5: piecewise-constant versus exact Jacobian
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKTaylor

open PDE AFree

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ} {π : Fin k → Vec d → ℝ}
  {ψ : Fin k → Vec k → ℝ} {Λ M : ℝ≥0} {μ : Measure (Vec d)}
  {R : ℝ} {δ : ℝ≥0} {r : ℝ} {F : Finset (Fin k → ℤ)}

/-- The constant `C₅ = k (√k M)^{k-1} √k` of Step 5. -/
noncomputable def jacConst (k : ℕ) (M : ℝ≥0) : ℝ :=
  k * (Real.sqrt k * M) ^ (k - 1) * Real.sqrt k

lemma abs_jacMat_sub_le {y y' : Vec k} {δ : ℝ≥0}
    (h : ∀ i, ‖fderiv ℝ (ψ i) y - fderiv ℝ (ψ i) y'‖ ≤ δ) (i l : Fin k) :
    |jacMat ψ y i l - jacMat ψ y' i l| ≤ δ := by
  have h1 : ‖(Pi.single l 1 : Vec k)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j; by_cases hj : j = l <;> simp [hj]
  have h2 := (fderiv ℝ (ψ i) y - fderiv ℝ (ψ i) y').le_opNorm (Pi.single l 1)
  simp only [sub_apply, Real.norm_eq_abs] at h2
  have := mul_le_mul (h i) h1 (norm_nonneg _) δ.coe_nonneg
  simp only [jacMat, Matrix.of_apply]
  linarith

lemma abs_det_jacMat_sub_le (cx : Ctx T π ψ Λ M μ) {y y' : Vec k} {δ : ℝ≥0}
    (h : ∀ i, ‖fderiv ℝ (ψ i) y - fderiv ℝ (ψ i) y'‖ ≤ δ) :
    |jacDet ψ y - jacDet ψ y'| ≤ jacConst k M * δ := by
  have := hadamard_abs_det_sub_le (jacMat ψ y) (jacMat ψ y') (M := Real.sqrt k * M)
    (δ := Real.sqrt k * δ) (piEuclideanNorm_jacMat_le cx y) (piEuclideanNorm_jacMat_le cx y')
    (fun i => by
      have := piEuclideanNorm_le_of_abs_le (jacMat ψ y i - jacMat ψ y' i) δ.coe_nonneg
        (fun l => abs_jacMat_sub_le h i l)
      simpa using this)
  unfold jacDet jacConst
  calc _ ≤ _ := this
    _ = _ := by ring

lemma abs_jacDet_sub_xi_le (cx : Ctx T π ψ Λ M μ) (sd : ScaleData ψ R δ r F) {y : Vec k}
    (hy : ‖y‖ ≤ R + 1) : |jacDet ψ y - xiFun ψ r F y| ≤ jacConst k M * δ := by
  have G := grid_partition_of_unity (m := k) sd.r_pos
  have hsum : ∑ J ∈ F, gridChi r J y = 1 := G.2.2.2.2.1 y F fun J hJ => (sd.mem J).2 ⟨y, hy, hJ⟩
  have hC : 0 ≤ jacConst k M * δ := by unfold jacConst; positivity
  have e : jacDet ψ y - xiFun ψ r F y =
      ∑ J ∈ F, gridChi r J y * (jacDet ψ y - (jacMat ψ (yJ r J)).det) := by
    have h1 : jacDet ψ y = ∑ J ∈ F, gridChi r J y * jacDet ψ y := by
      rw [← Finset.sum_mul, hsum, one_mul]
    have h2 : xiFun ψ r F y = ∑ J ∈ F, gridChi r J y * (jacMat ψ (yJ r J)).det :=
      Finset.sum_congr rfl fun J _ => mul_comm _ _
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← h1, ← h2]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ J ∈ F, gridChi r J y * (jacConst k M * δ) := Finset.sum_le_sum fun J hJ => ?_
    _ = jacConst k M * δ := by rw [← Finset.sum_mul, hsum, one_mul]
  by_cases hχ : gridChi r J y = 0
  · simp [hχ]
  · rw [abs_mul, abs_of_nonneg (G.2.1 J y).1]
    refine mul_le_mul_of_nonneg_left ?_ (G.2.1 J y).1
    have hyJ := sd.norm_yJ_le hJ
    have hnear : ‖y - yJ r J‖ ≤ 2 * r := by
      have h := G.2.2.2.1 J y hχ
      have : ‖y - yJ r J‖ ≤ r := (pi_norm_le_iff_of_nonneg sd.r_pos.le).2 fun l => by
        simpa [yJ, Real.norm_eq_abs] using (h l).le
      linarith [sd.r_pos]
    exact abs_det_jacMat_sub_le cx (sd.mod y (yJ r J) (by linarith) (by linarith) hnear)

lemma borelBdd_sub {h g : Vec d → ℝ} (hh : IsBorelBdd h) (hg : IsBorelBdd g) :
    IsBorelBdd (fun x => h x - g x) := by
  refine ⟨hh.1.sub hg.1, ?_⟩
  obtain ⟨C, hC⟩ := hh.2
  obtain ⟨C', hC'⟩ := hg.2
  exact ⟨C + C', fun x => (abs_sub _ _).trans (add_le_add (hC x) (hC' x))⟩

lemma lipb_xi_comp (cx : Ctx T π ψ Λ M μ) (sd : ScaleData ψ R δ r F) :
    IsBddLipFun (fun x => xiFun ψ r F (evalTuple π x)) := by
  unfold xiFun
  refine lipb_sum F fun J _ => ?_
  exact lipb_smul _ (lipb_gridChi_comp cx sd.r_pos J)

/-- Step 5. The piecewise-constant Jacobian `ξ` is `C₅ δ`-close to
`det Dψ` on `{‖y‖ ≤ R + 1}` (Hadamard), hence
`|T(f_R det Dψ(π), π) - T(f_R ξ(π), π)| ≤ ∏Λ · C₅ δ ∫ |f| dμ_T`. -/
theorem frozen_vs_exact (cx : Ctx T π ψ Λ M μ) (sd : ScaleData ψ R δ r F) {f : Vec d → ℝ}
    (hf : IsBddLipFun f) :
    |akExt T (jacW ψ π (cutoffWeight π R f)) π -
        T (fun x => cutoffWeight π R f x * xiFun ψ r F (evalTuple π x)) π| ≤
      (Λ : ℝ) ^ k * (jacConst k M * δ) * ∫ x, |f x| ∂μ := by
  have := cx.hμ.1.1
  set g := cutoffWeight π R f with hgdef
  have hg : IsBddLipFun g := lipb_cutoffWeight cx R hf
  have hh' : IsBddLipFun (fun x => g x * xiFun ψ r F (evalTuple π x)) :=
    lipb_mul hg (lipb_xi_comp cx sd)
  have hBh : IsBorelBdd (jacW ψ π g) := borelBdd_mul_jacDet cx (borelBdd_of_lipb hg)
  have hBh' := borelBdd_of_lipb hh'
  obtain ⟨E1, E2, -, -⟩ := (akext cx.hT).1
  have e1 := E1 _ hh' π cx.isLipTuple
  have e2 : (fun x => jacW ψ π g x - g x * xiFun ψ r F (evalTuple π x)) =
      (1 : ℝ) • jacW ψ π g + (-1 : ℝ) • (fun x => g x * xiFun ψ r F (evalTuple π x)) := by
    funext x; simp; ring
  have hdiffB : IsBorelBdd (fun x => jacW ψ π g x - g x * xiFun ψ r F (evalTuple π x)) :=
    borelBdd_sub hBh hBh'
  have hsub : akExt T (fun x => jacW ψ π g x - g x * xiFun ψ r F (evalTuple π x)) π =
      akExt T (jacW ψ π g) π - akExt T (fun x => g x * xiFun ψ r F (evalTuple π x)) π := by
    rw [e2, E2 π cx.isLipTuple _ _ hBh hBh']; ring
  rw [← e1, ← hsub]
  have h3 := abs_akExt_le cx hdiffB (π' := π) (K := fun _ => Λ) cx.hπ
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h3
  have hC : 0 ≤ jacConst k M * δ := by unfold jacConst; positivity
  have hint : ∫ x, |jacW ψ π g x - g x * xiFun ψ r F (evalTuple π x)| ∂μ ≤
      (jacConst k M * δ) * ∫ x, |f x| ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
      ((integrable_of_borelBdd (borelBdd_of_lipb hf)).abs.const_mul _)
      (Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hg0 : g x = 0
    · simp only [jacW, hg0, zero_mul, sub_zero, abs_zero]
      exact mul_nonneg hC (abs_nonneg _)
    · have hθ : theta R (evalTuple π x) ≠ 0 := right_ne_zero_of_mul hg0
      have hb := abs_jacDet_sub_xi_le cx sd (ne_zero_imp_norm_lt hθ).le
      have habs : |g x| ≤ |f x| := by
        rw [hgdef]; unfold cutoffWeight
        rw [abs_mul, abs_of_nonneg (theta_nonneg _ _)]
        exact mul_le_of_le_one_right (abs_nonneg _) (theta_le_one _ _)
      have : jacW ψ π g x - g x * xiFun ψ r F (evalTuple π x) =
          g x * (jacDet ψ (evalTuple π x) - xiFun ψ r F (evalTuple π x)) := by
        simp only [jacW]; ring
      rw [this, abs_mul]
      calc |g x| * |jacDet ψ (evalTuple π x) - xiFun ψ r F (evalTuple π x)|
          ≤ |f x| * (jacConst k M * δ) :=
            mul_le_mul habs hb (abs_nonneg _) (abs_nonneg _)
        _ = _ := by ring
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) ^ k := pow_nonneg Λ.coe_nonneg _
  calc _ ≤ _ := h3
    _ ≤ (Λ : ℝ) ^ k * ((jacConst k M * δ) * ∫ x, |f x| ∂μ) :=
        mul_le_mul_of_nonneg_left hint hΛ
    _ = _ := by ring

end AFree.MetricCurrents.AKTaylor
