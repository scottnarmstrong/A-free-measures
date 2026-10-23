module

public import AFree.Analysis.KernelBound
public import AFree.Analysis.ConvCompact
public import AFree.Analysis.Fava
public import CZStatements.WeakType.NewtonMatRepresentation
public import CZStatements.WeakType.NewtonMatWeakType
public import CZStatements.WeakType.NewtonMatPotentialSmooth
public import CZStatements.WeakType.NewtonMatPotentialLinear

/-!
# Strong constancy

Strong constancy for first-order operators in the proof of [DPR, Theorem 1.1]: representation `w_j = f_j + h_j`, weak-type
smallness of `f_j`, `L¹` compactness of `h_j`, distributional smallness of `f_j`, and the
Vitali lemma.
-/

@[expose] public section

open MeasureTheory PDE Filter Topology

namespace AFree

noncomputable section

variable {d : ℕ}

/-- Domination preserves uniform integrability in `L¹`. -/
theorem unifIntegrable_one_of_norm_le {μ : Measure (Vec d)} {f g : ℕ → Vec d → ℝ}
    (hf : UnifIntegrable f 1 μ) (hgm : ∀ i, AEStronglyMeasurable (g i) μ)
    (hg : ∀ i x, ‖g i x‖ ≤ ‖f i x‖) :
    UnifIntegrable g 1 μ := by
  rw [unifIntegrable_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf ε hε
  exact ⟨δ, hδ, fun i s hs =>
    (eLpNorm_mono (hgm i).restrict (fun x => hg i x)).trans (h i s hs)⟩

/-- Integration by parts for a smooth compactly supported `ψ` against a smooth `u`. -/
theorem integral_mul_euclideanCoordDeriv_eq_neg {ψ u : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (k : Fin d) :
    ∫ x, ψ x * euclideanCoordDeriv k u x = -∫ x, euclideanCoordDeriv k ψ x * u x := by
  have hψ' := contDiff_euclideanCoordDeriv hψ k
  have hu' := contDiff_euclideanCoordDeriv hu k
  have hψ'c := hasCompactSupport_euclideanCoordDeriv hψc k
  have h1 : Integrable fun x => euclideanCoordDeriv k ψ x * u x :=
    (hψ'.continuous.mul hu.continuous).integrable_of_hasCompactSupport hψ'c.mul_right
  have h2 : Integrable fun x => ψ x * euclideanCoordDeriv k u x :=
    (hψ.continuous.mul hu'.continuous).integrable_of_hasCompactSupport hψc.mul_right
  have h3 : Integrable fun x => ψ x * u x :=
    (hψ.continuous.mul hu.continuous).integrable_of_hasCompactSupport hψc.mul_right
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := basisVec k) h1 h2 h3
    (fun x _ => (hψ.differentiable (by simp)) x) (fun x _ => (hu.differentiable (by simp)) x)

theorem hasCompactSupport_of_tsupport_subset_ball {F : Vec d → Vec d}
    (hFs : tsupport F ⊆ euclideanBall (0 : Vec d) 1) : HasCompactSupport F :=
  (isCompact_euclideanClosedBall (0 : Vec d) zero_le_one).of_isClosed_subset (isClosed_tsupport _)
    (hFs.trans (euclideanBall_subset_euclideanClosedBall _ _))

theorem integrable_of_tsupport_subset_ball {F : Vec d → Vec d} (hF : Continuous F)
    (hFs : tsupport F ⊆ euclideanBall (0 : Vec d) 1) : Integrable F :=
  hF.integrable_of_hasCompactSupport (hasCompactSupport_of_tsupport_subset_ball hFs)

/-- The potential `u^M_F` is integrable on `B₁` for `F` supported in `B₁`. -/
theorem integrableOn_ball_newtonPotentialMat {Λ : ℝ} {M : Mat d} (hd : 0 < d) (hΛ : 0 < Λ)
    (hMs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    {F : Vec d → Vec d} (hF : Continuous F) (hFs : tsupport F ⊆ euclideanBall (0 : Vec d) 1) :
    IntegrableOn (newtonPotentialMat M F) (euclideanBall (0 : Vec d) 1) := by
  have := ((integrable_conv (integrable_truncKernel hΛ hMs hM hd)
    (integrable_of_tsupport_subset_ball hF hFs)).integrableOn (s := euclideanBall (0 : Vec d) 1))
  exact this.congr_fun (fun x hx => (newtonPotentialMat_eq_truncKernel hFs hx).symm)
    (measurableSet_euclideanBall _ _)

/-- Step 1: representation `w = Σ ∂_ℓ u^M_{G^ℓ} + u^M_H`. -/
theorem eq_sum_add_of_div_eq {Λ : ℝ} {M : Mat d} (hd : 0 < d) (hΛ : 0 < Λ) (hMs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    {w : Vec d → ℝ} {G : Fin d → Vec d → Vec d} {H : Vec d → Vec d}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hG : ∀ ℓ, ContDiff ℝ (⊤ : ℕ∞) (G ℓ))
    (hGs : ∀ ℓ, tsupport (G ℓ) ⊆ euclideanBall (0 : Vec d) 1)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHs : tsupport H ⊆ euclideanBall (0 : Vec d) 1)
    (heq : ∀ x, classicalDivergence (fun y => matVecMul M (classicalGradient w y)) x =
      classicalDivergence
        (fun y => (∑ ℓ, fun i => euclideanCoordDeriv ℓ (fun z => G ℓ z i) y) + H y) x) :
    ∀ x, w x = (∑ ℓ, euclideanCoordDeriv ℓ (newtonPotentialMat M (G ℓ)) x) +
      newtonPotentialMat M H x := by
  set DG : Fin d → Vec d → Vec d := fun ℓ y i => euclideanCoordDeriv ℓ (fun z => G ℓ z i) y
    with hDG
  have hDGs : ∀ ℓ, ContDiff ℝ (⊤ : ℕ∞) (DG ℓ) := fun ℓ =>
    contDiff_pi.2 fun i => contDiff_euclideanCoordDeriv ((contDiff_pi.1 (hG ℓ)) i) ℓ
  have hDGc : ∀ ℓ, HasCompactSupport (DG ℓ) := fun ℓ => by
    refine (isCompact_euclideanClosedBall (0 : Vec d) zero_le_one).of_isClosed_subset
      isClosed_closure (closure_minimal ?_ (isClosed_euclideanClosedBall _ _))
    intro y hy
    obtain ⟨i, hi⟩ : ∃ i, DG ℓ y i ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (funext h)
    have h1 := support_euclideanCoordDeriv_subset_tsupport ℓ (fun z => G ℓ z i) hi
    have h2 : tsupport (fun z => G ℓ z i) ⊆ tsupport (G ℓ) :=
      closure_mono fun z hz h => hz (by simp [h])
    exact euclideanBall_subset_euclideanClosedBall _ _ (hGs ℓ (h2 h1))
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun y => (∑ ℓ, fun i => euclideanCoordDeriv ℓ
      (fun z => G ℓ z i) y) + H y) :=
    (ContDiff.sum fun ℓ _ => hDGs ℓ).add hH
  have hHc := hasCompactSupport_of_tsupport_subset_ball hHs
  have hΦc : HasCompactSupport (fun y => (∑ ℓ, fun i => euclideanCoordDeriv ℓ
      (fun z => G ℓ z i) y) + H y) := by
    have hs : ∀ s : Finset (Fin d), HasCompactSupport (fun y => ∑ ℓ ∈ s, DG ℓ y) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using HasCompactSupport.intro isCompact_empty (by simp)
      | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (hDGc a).add ih
    exact (hs Finset.univ).add hHc
  have hrep := PDE.eq_newtonPotentialMat_of_div_eq_div d hd Λ hΛ M hMs hM w _ hw hwc hΦ hΦc heq
  intro x
  have hlin := PDE.newtonPotentialMat_linearCombination (ι := Option (Fin d)) d hd Λ hΛ M hMs hM
    Finset.univ (fun _ => (1 : ℝ)) (fun o => o.elim H DG)
    (fun o _ => by cases o <;> simp [hH.continuous, (hDGs _).continuous])
    (fun o _ => by cases o <;> simp [hHc, hDGc])
  have hfun : (fun y => (∑ ℓ, fun i => euclideanCoordDeriv ℓ (fun z => G ℓ z i) y) + H y) =
      ∑ o ∈ (Finset.univ : Finset (Option (Fin d))), (fun _ => (1 : ℝ)) o • (fun o : Option (Fin d) => o.elim H DG) o := by
    funext y
    simp [Fintype.sum_option, hDG, add_comm]
  rw [hfun] at hrep
  rw [hrep, hlin]
  simp only [Finset.sum_apply, Fintype.sum_option, one_smul]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  exact ((PDE.contDiff_newtonPotentialMat_and_coordDeriv d hd Λ hΛ M hMs hM (G ℓ) (hG ℓ)
    (hasCompactSupport_of_tsupport_subset_ball (hGs ℓ))).2 ℓ x).symm

/-- Step 2: weak-type bound for `f = Σ ∂_ℓ u^M_{G^ℓ}`. -/
theorem volume_setOf_lt_abs_sum_le {M : Mat d} (hd : 0 < d) {C : ℝ}
    (hC : ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ euclideanBall (0 : Vec d) 1 → ∀ lam : ℝ, 0 < lam →
        volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
          lam < vecEuclideanNorm (classicalGradient (newtonPotentialMat M F) x)} ≤
          ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)))
    (hC0 : 0 ≤ C)
    {G : Fin d → Vec d → Vec d} (hG : ∀ ℓ, ContDiff ℝ (⊤ : ℕ∞) (G ℓ))
    (hGs : ∀ ℓ, tsupport (G ℓ) ⊆ euclideanBall (0 : Vec d) 1) {lam : ℝ} (hlam : 0 < lam) :
    volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
        lam < |∑ ℓ, euclideanCoordDeriv ℓ (newtonPotentialMat M (G ℓ)) x|} ≤
      ENNReal.ofReal (C * d / lam * ∑ ℓ, ∫ x, vecEuclideanNorm (G ℓ x)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsub : {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
        lam < |∑ ℓ, euclideanCoordDeriv ℓ (newtonPotentialMat M (G ℓ)) x|} ⊆
      ⋃ ℓ ∈ (Finset.univ : Finset (Fin d)), {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
        lam / d < vecEuclideanNorm (classicalGradient (newtonPotentialMat M (G ℓ)) x)} := by
    rintro x ⟨hx, hlt⟩
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_univ, exists_true_left, not_exists,
      not_and, not_lt] at hcon
    have hb : ∀ ℓ, |euclideanCoordDeriv ℓ (newtonPotentialMat M (G ℓ)) x| ≤ lam / d := fun ℓ =>
      (abs_apply_le_vecEuclideanNorm _ ℓ).trans (hcon ℓ hx)
    have : |∑ ℓ, euclideanCoordDeriv ℓ (newtonPotentialMat M (G ℓ)) x| ≤ lam := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun ℓ _ => hb ℓ).trans ?_
      simp [Finset.sum_const, Finset.card_univ]
      field_simp
      exact le_rfl
    linarith
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have h1 : ∀ ℓ ∈ (Finset.univ : Finset (Fin d)), volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
        lam / d < vecEuclideanNorm (classicalGradient (newtonPotentialMat M (G ℓ)) x)} ≤
      ENNReal.ofReal (C * d / lam * ∫ x, vecEuclideanNorm (G ℓ x)) := by
    intro ℓ _
    refine (hC (G ℓ) (hG ℓ) (hGs ℓ) _ (by positivity)).trans (le_of_eq ?_)
    congr 1
    field_simp
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg, ← Finset.mul_sum]
  intro ℓ _
  exact mul_nonneg (by positivity) (integral_nonneg fun x => vecEuclideanNorm_nonneg _)

/-- Step 4: the distributional estimate. -/
theorem abs_integral_mul_coordDeriv_le {Λ : ℝ} {M : Mat d} (hd : 0 < d) (hΛ : 0 < Λ)
    (hMs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    {G : Vec d → Vec d} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGs : tsupport G ⊆ euclideanBall (0 : Vec d) 1)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ euclideanBall (0 : Vec d) 1) (ℓ : Fin d) {B : ℝ}
    (hB : ∀ x, |euclideanCoordDeriv ℓ ψ x| ≤ B) :
    |∫ x, ψ x * euclideanCoordDeriv ℓ (newtonPotentialMat M G) x| ≤
      B * (truncKernelNorm M * ∫ x, vecEuclideanNorm (G x)) := by
  have hGc := hasCompactSupport_of_tsupport_subset_ball hGs
  have hU := (PDE.contDiff_newtonPotentialMat_and_coordDeriv d hd Λ hΛ M hMs hM G hG hGc).1
  rw [integral_mul_euclideanCoordDeriv_eq_neg hψ hψc hU, abs_neg]
  set B1 := euclideanBall (0 : Vec d) 1
  have hB1m : MeasurableSet B1 := measurableSet_euclideanBall _ _
  have hsupp : ∀ x ∉ B1, euclideanCoordDeriv ℓ ψ x * newtonPotentialMat M G x = 0 := by
    intro x hx
    have : euclideanCoordDeriv ℓ ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hx (hψs (tsupport_euclideanCoordDeriv_subset_tsupport ℓ ψ h))
    simp [this]
  have hK : IsCompact (euclideanClosedBall (0 : Vec d) 1) :=
    isCompact_euclideanClosedBall _ zero_le_one
  have hUi : IntegrableOn (newtonPotentialMat M G) B1 :=
    (hU.continuous.locallyIntegrable.integrableOn_isCompact hK).mono_set
      (euclideanBall_subset_euclideanClosedBall _ _)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x in B1, |euclideanCoordDeriv ℓ ψ x * newtonPotentialMat M G x|
      ≤ ∫ x in B1, B * |newtonPotentialMat M G x| :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (hUi.abs.const_mul B) (Filter.Eventually.of_forall fun x => by
            beta_reduce; rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _))
    _ = B * ∫ x in B1, |newtonPotentialMat M G x| := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (integral_abs_newtonPotentialMat_le hΛ hMs hM hd hG.continuous hGs) hB0

/-- Strong constancy. -/
theorem exists_subseq_tendsto_L1_of_elliptic {d : ℕ} (hd : 0 < d) {Λ : ℝ} (hΛ : 0 < Λ)
    {M : Mat d} (hMs : M.IsSymm)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
      vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (w : ℕ → Vec d → ℝ) (G : ℕ → Fin d → Vec d → Vec d) (H : ℕ → Vec d → Vec d)
    (hw : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (w j)) (hwc : ∀ j, HasCompactSupport (w j))
    (hw0 : ∀ j x, 0 ≤ w j x) (hwsupp : ∀ j, tsupport (w j) ⊆ euclideanClosedBall 0 (3/4))
    (hG : ∀ j ℓ, ContDiff ℝ (⊤ : ℕ∞) (G j ℓ))
    (hGsupp : ∀ j ℓ, tsupport (G j ℓ) ⊆ euclideanBall 0 1)
    (hH : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (H j)) (hHsupp : ∀ j, tsupport (H j) ⊆ euclideanBall 0 1)
    (heq : ∀ j x, PDE.classicalDivergence
        (fun y => PDE.matVecMul M (PDE.classicalGradient (w j) y)) x =
      PDE.classicalDivergence
        (fun y => (∑ ℓ, fun i => euclideanCoordDeriv ℓ (fun z => G j ℓ z i) y) + H j y) x)
    (hGsmall : Tendsto (fun j => ∑ ℓ, ∫ x, vecEuclideanNorm (G j ℓ x)) atTop (𝓝 0))
    (hHbdd : ∃ C, ∀ j, ∫ x, vecEuclideanNorm (H j x) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ wInf : Vec d → ℝ, Integrable wInf ∧
      Tendsto (fun i => ∫ x, |w (φ i) x - wInf x|) atTop (𝓝 0) := by
  obtain ⟨C, hCpos, hCw⟩ := PDE.exists_newtonPotentialMat_weakTypeOne d hd Λ hΛ
  have hCw' := hCw M hMs hM
  set B1 := euclideanBall (0 : Vec d) 1 with hB1
  have hB1m : MeasurableSet B1 := measurableSet_euclideanBall _ _
  have hB1B2 : B1 ⊆ euclideanBall (0 : Vec d) 2 := by
    intro x hx
    rw [hB1, mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos, sub_zero] at hx
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt two_pos, sub_zero]
    linarith
  have hrep := fun j => eq_sum_add_of_div_eq hd hΛ hMs hM (hw j) (hwc j) (hG j) (hGsupp j)
    (hH j) (hHsupp j) (heq j)
  set S : ℕ → ℝ := fun j => ∑ ℓ, ∫ x, vecEuclideanNorm (G j ℓ x) with hS
  have hf : ∀ j x, w j x - newtonPotentialMat M (H j) x =
      ∑ ℓ, euclideanCoordDeriv ℓ (newtonPotentialMat M (G j ℓ)) x := fun j x => by
    rw [hrep j x]; ring
  -- Step 2
  have hmeas : ∀ lam : ℝ, 0 < lam → Tendsto (fun j => volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
      lam < |w j x - newtonPotentialMat M (H j) x|}) atTop (𝓝 0) := by
    intro lam hlam
    have hup : Tendsto (fun j => ENNReal.ofReal (C * d / lam * S j)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (hGsmall.const_mul (C * d / lam))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => bot_le)
      (fun j => ?_)
    have := volume_setOf_lt_abs_sum_le (M := M) hd hCw' hCpos.le (hG j) (hGsupp j) hlam
    simpa only [hf] using this
  -- Step 3
  obtain ⟨Cb, hCb⟩ := hHbdd
  obtain ⟨φ, hφ, g, hg, hgt⟩ := exists_subseq_tendsto_conv (k := truncKernel M)
    (integrable_truncKernel hΛ hMs hM hd) (F := H)
    (fun j => integrable_of_tsupport_subset_ball (hH j).continuous (hHsupp j)) hCb
  have hgt' : Tendsto (fun i => ∫ x in B1, |newtonPotentialMat M (H (φ i)) x - g x|) atTop
      (𝓝 0) := by
    refine hgt.congr fun i => setIntegral_congr_fun hB1m fun x hx => ?_
    rw [newtonPotentialMat_eq_truncKernel (hHsupp _) hx]
    rfl
  have hUH : ∀ i, IntegrableOn (newtonPotentialMat M (H (φ i))) B1 := fun i =>
    integrableOn_ball_newtonPotentialMat hd hΛ hMs hM (hH _).continuous (hHsupp _)
  have hwi : ∀ j, Integrable (w j) := fun j =>
    (hw j).continuous.integrable_of_hasCompactSupport (hwc j)
  set fi : ℕ → Vec d → ℝ := fun i x => w (φ i) x - newtonPotentialMat M (H (φ i)) x with hfi
  have hint : ∀ i, IntegrableOn (fi i) B1 := fun i => (hwi _).integrableOn.sub (hUH i)
  have hSφ : Tendsto (fun i => S (φ i)) atTop (𝓝 0) := hGsmall.comp hφ.tendsto_atTop
  -- Step 4
  have ha : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ B1 → Tendsto (fun i => ∫ x, ψ x * fi i x) atTop (𝓝 0) := by
    intro ψ hψ hψc hψs
    have hbd : ∀ ℓ, ∃ b : ℝ, ∀ x, |euclideanCoordDeriv ℓ ψ x| ≤ b := fun ℓ => by
      obtain ⟨b, hb⟩ :=
        (contDiff_euclideanCoordDeriv hψ ℓ).continuous.bounded_above_of_compact_support
          (hasCompactSupport_euclideanCoordDeriv hψc ℓ)
      exact ⟨b, fun x => by simpa using hb x⟩
    choose b hb using hbd
    have hb0 : ∀ ℓ, 0 ≤ b ℓ := fun ℓ => (abs_nonneg _).trans (hb ℓ 0)
    set Bb := ∑ ℓ, b ℓ with hBb
    have hbB : ∀ ℓ, b ℓ ≤ Bb := fun ℓ =>
      Finset.single_le_sum (f := b) (fun ℓ _ => hb0 ℓ) (Finset.mem_univ ℓ)
    refine squeeze_zero_norm (a := fun i => Bb * truncKernelNorm M * S (φ i))
      (fun i => ?_) (by simpa using (hSφ.const_mul (Bb * truncKernelNorm M)))
    have hU : ∀ ℓ, ContDiff ℝ (⊤ : ℕ∞) (newtonPotentialMat M (G (φ i) ℓ)) := fun ℓ =>
      (PDE.contDiff_newtonPotentialMat_and_coordDeriv d hd Λ hΛ M hMs hM _ (hG _ _)
        (hasCompactSupport_of_tsupport_subset_ball (hGsupp _ _))).1
    have hD : ∀ ℓ, Integrable fun x =>
        ψ x * euclideanCoordDeriv ℓ (newtonPotentialMat M (G (φ i) ℓ)) x := fun ℓ =>
      (hψ.continuous.mul (contDiff_euclideanCoordDeriv (hU ℓ) ℓ).continuous
        ).integrable_of_hasCompactSupport hψc.mul_right
    have e1 : ∫ x, ψ x * fi i x = ∑ ℓ, ∫ x, ψ x *
        euclideanCoordDeriv ℓ (newtonPotentialMat M (G (φ i) ℓ)) x := by
      rw [← integral_finsetSum _ fun ℓ _ => hD ℓ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hfi]
      rw [hf, Finset.mul_sum]
    rw [e1, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ ℓ, Bb * (truncKernelNorm M * ∫ x, vecEuclideanNorm (G (φ i) ℓ x)) :=
          Finset.sum_le_sum fun ℓ _ => (abs_integral_mul_coordDeriv_le hd hΛ hMs hM (hG _ _)
            (hGsupp _ _) hψ hψc hψs ℓ (fun x => (hb ℓ x).trans (hbB ℓ)))
      _ = _ := by simp only [hS, mul_assoc, ← Finset.mul_sum]
  -- Step 5
  have hb : ∀ l : ℝ, 0 < l → Tendsto (fun i => volume {x ∈ B1 | l < max (-fi i x) 0}) atTop
      (𝓝 0) := by
    intro l hl
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((hmeas l hl).comp hφ.tendsto_atTop) (fun _ => bot_le) (fun i => measure_mono ?_)
    rintro x ⟨hx, hlt⟩
    refine ⟨hB1B2 hx, ?_⟩
    have : l < -fi i x := by
      rcases max_cases (-fi i x) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hlt <;> linarith
    exact lt_abs.2 (Or.inr this)
  have hL1 : Tendsto (fun i => eLpNorm ((fun x => newtonPotentialMat M (H (φ i)) x) - g) 1
      (volume.restrict B1)) atTop (𝓝 0) := by
    have h1 : ∀ i, eLpNorm ((fun x => newtonPotentialMat M (H (φ i)) x) - g) 1
        (volume.restrict B1) = ENNReal.ofReal (∫ x in B1, |newtonPotentialMat M (H (φ i)) x
          - g x|) := fun i => by
      rw [eLpNorm_one_eq_lintegral_enorm ((hUH i).sub hg).aestronglyMeasurable, ← ofReal_integral_norm_eq_lintegral_enorm
        ((hUH i).sub hg)]
      simp only [Pi.sub_apply, Real.norm_eq_abs]
    simp only [h1]
    simpa using ENNReal.tendsto_ofReal hgt'
  have hunif := unifIntegrable_of_tendsto_Lp (μ := volume.restrict B1)
    (f := fun i x => newtonPotentialMat M (H (φ i)) x) le_rfl ENNReal.one_ne_top
    (fun i => memLp_one_iff_integrable.2 (hUH i)) (memLp_one_iff_integrable.2 hg) hL1
  have hc : UnifIntegrable (fun i => fun x => max (-fi i x) 0) 1 (volume.restrict B1) :=
    unifIntegrable_one_of_norm_le hunif (fun i => ((hint i).neg.pos_part).aestronglyMeasurable)
      (fun i x => by
        have h1 := hw0 (φ i) x
        simp only [hfi, Real.norm_eq_abs]
        rw [abs_of_nonneg (le_max_right _ _)]
        refine max_le ?_ (abs_nonneg _)
        have := le_abs_self (newtonPotentialMat M (H (φ i)) x)
        linarith)
  -- Step 6
  set K := euclideanClosedBall (0 : Vec d) (3 / 4) with hK
  have hKc : IsCompact K := isCompact_euclideanClosedBall _ (by norm_num)
  have hKB : K ⊆ B1 := euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num)
  have hV := tendsto_setIntegral_abs_of_vitali fi hint ha hb hc hKc hKB
  have hKm : MeasurableSet K := hKc.measurableSet
  refine ⟨φ, hφ, K.indicator g, (hg.mono_set hKB).integrable_indicator hKm, ?_⟩
  refine squeeze_zero (fun i => integral_nonneg fun x => abs_nonneg _) (fun i => ?_)
    (by simpa using hV.add hgt')
  have hgK : IntegrableOn g K := hg.mono_set hKB
  have hsupp : ∀ x ∉ K, |w (φ i) x - K.indicator g x| = 0 := by
    intro x hx
    have : w (φ i) x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hwsupp _ h)
    simp [this, Set.indicator_of_notMem hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) hsupp]
  have hfK : IntegrableOn (fun x => |fi i x|) K := ((hint i).mono_set hKB).abs
  have hhK : IntegrableOn (fun x => |newtonPotentialMat M (H (φ i)) x - g x|) B1 :=
    ((hUH i).sub hg).abs
  calc ∫ x in K, |w (φ i) x - K.indicator g x|
      ≤ ∫ x in K, (|fi i x| + |newtonPotentialMat M (H (φ i)) x - g x|) := by
        refine setIntegral_mono_on ?_ (hfK.add (hhK.mono_set hKB)) hKm fun x hx => ?_
        · have h0 : IntegrableOn (fun x => |w (φ i) x - g x|) K :=
            (((hwi (φ i)).integrableOn).sub hgK).abs
          exact h0.congr_fun (fun x hx => by simp [Set.indicator_of_mem hx]) hKm
        · rw [Set.indicator_of_mem hx]
          have : w (φ i) x - g x = fi i x + (newtonPotentialMat M (H (φ i)) x - g x) := by
            simp only [hfi]; ring
          rw [this]
          exact abs_add_le _ _
    _ = (∫ x in K, |fi i x|) + ∫ x in K, |newtonPotentialMat M (H (φ i)) x - g x| :=
        integral_add hfK (hhK.mono_set hKB)
    _ ≤ _ := by
        exact add_le_add le_rfl (setIntegral_mono_set hhK
          (Filter.Eventually.of_forall fun x => abs_nonneg _) (Filter.Eventually.of_forall hKB))

end

end AFree
