module

public import AFree.Paper.Elliptic.Calculus
public import AFree.Paper.Elliptic.Mollified
public import AFree.Paper.Elliptic.Leibniz
public import PDEFoundation.Analysis.Newtonian.Defs

/-!
# The mollified elliptic system

The mollified blow-ups satisfy an elliptic system with small right-hand side, for one radius
`r ∈ (0,1]` and one scale `ε ∈ (0,1/8]` ([DPR, proof of Theorem 1.1]).

* `AFree.mollified_equation` is the mollified equation (in `Elliptic.Mollified`);
* `AFree.mollU`, `AFree.mollMu`, `AFree.mollV` are the mollified objects `u`, `μ^ε`, `V`;
* `AFree.integral_mollU_le_one`, `AFree.integral_mollV_le`, `AFree.integral_mollMu_le` are the
  three `L¹` smallness bounds;
* `AFree.leibniz_system` and `AFree.leibniz_bounds` are the cut-off system and its bounds.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal

namespace AFree

open PDE

variable {d m n : ℕ}

lemma vecCoordDeriv_eq_fderiv {f : Vec d → Vec m} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ℓ : Fin d)
    (x : Vec d) : vecCoordDeriv ℓ f x = fderiv ℝ f x (basisVec ℓ) := by
  funext i
  have h := (hasFDerivAt_pi'.1 ((hf.differentiable (by simp)) x).hasFDerivAt i).fderiv
  simp only [vecCoordDeriv, euclideanCoordDeriv]
  rw [h]
  rfl

/-- Qualitative part, for the mollified blow-ups `μ^ε`, `u`, `V = μ^ε − u P₀`,
`w = χ u`, `G^{(ℓ)}`, `H` of the mollified construction. Hypotheses: those of the mollified equation (`(σ,P)` is
`𝒜`-free, `Q_r(x₀) ⊆ Ω`, `P ∈ L¹(σ)`, `σ` finite, `c < ∞`), and `ε ∈ (0,1/8]`. The final
conjunct is the `heq` shape of `exists_subseq_tendsto_L1_of_elliptic`. -/
theorem leibniz_system {Ω : Set (Vec d)} {A : Fin d → Matrix (Fin n) (Fin m) ℝ}
    {A₀ : Matrix (Fin n) (Fin m) ℝ} {σ : Measure (Vec d)} [IsFiniteMeasure σ]
    {P : Vec d → Vec m} (h : IsFreePair Ω A A₀ σ P) (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (hΩ : Metric.closedBall x₀ r ⊆ Ω) {c : ℝ≥0∞} (hc : c ≠ ∞) (hP : Integrable P σ)
    (P₀ : Vec m) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    (∀ x, 0 ≤ leibnizW (mollU x₀ r c ε σ) x) ∧
    ContDiff ℝ (⊤ : ℕ∞) (leibnizW (mollU x₀ r c ε σ)) ∧
    tsupport (leibnizW (mollU x₀ r c ε σ)) ⊆ euclideanClosedBall (0 : Vec d) (3 / 4) ∧
    (∀ ℓ, ContDiff ℝ (⊤ : ℕ∞) (leibnizG A P₀ (mollV x₀ r c ε σ P P₀) ℓ) ∧
      tsupport (leibnizG A P₀ (mollV x₀ r c ε σ P P₀) ℓ) ⊆ euclideanBall (0 : Vec d) 1) ∧
    ContDiff ℝ (⊤ : ℕ∞)
      (leibnizH A A₀ P₀ r (mollMu x₀ r c ε σ P) (mollU x₀ r c ε σ) (mollV x₀ r c ε σ P P₀)) ∧
    tsupport (leibnizH A A₀ P₀ r (mollMu x₀ r c ε σ P) (mollU x₀ r c ε σ)
      (mollV x₀ r c ε σ P P₀)) ⊆ euclideanBall (0 : Vec d) 1 ∧
    (∀ x, matVecMul (ellipticMatrix A P₀) (classicalGradient (leibnizW (mollU x₀ r c ε σ)) x) =
      (∑ ℓ, fun i => euclideanCoordDeriv ℓ (fun z => leibnizG A P₀ (mollV x₀ r c ε σ P P₀) ℓ z i) x) +
        leibnizH A A₀ P₀ r (mollMu x₀ r c ε σ P) (mollU x₀ r c ε σ) (mollV x₀ r c ε σ P P₀) x) ∧
    (∀ x, classicalDivergence
        (fun y => matVecMul (ellipticMatrix A P₀)
          (classicalGradient (leibnizW (mollU x₀ r c ε σ)) y)) x =
      classicalDivergence
        (fun y => (∑ ℓ, fun i =>
            euclideanCoordDeriv ℓ (fun z => leibnizG A P₀ (mollV x₀ r c ε σ P P₀) ℓ z i) y) +
          leibnizH A A₀ P₀ r (mollMu x₀ r c ε σ P) (mollU x₀ r c ε σ)
            (mollV x₀ r c ε σ P P₀) y) x) := by
  have hμ := contDiff_mollMu hr hc hP hε (x₀ := x₀)
  have hu := contDiff_mollU hc hε (σ := σ) (x₀ := x₀) (r := r)
  have hV := contDiff_mollV hr hc hP hε P₀ (x₀ := x₀)
  have hpde : ∀ x ∈ euclideanBall (0 : Vec d) (7 / 8),
      (∑ ℓ, A ℓ *ᵥ vecCoordDeriv ℓ (mollMu x₀ r c ε σ P) x) +
        r • (A₀ *ᵥ mollMu x₀ r c ε σ P x) = 0 := by
    intro x hx
    have := mollified_equation h x₀ hr hΩ hc hP hε hε8 hx
    simp only [vecCoordDeriv_eq_fderiv hμ]
    exact this
  have hid := leibniz_identity (A := A) (A₀ := A₀) (P₀ := P₀) (r := r) hμ hu
    (fun x => rfl) hpde
  refine ⟨leibnizW_nonneg (mollU_nonneg hε.le σ), contDiff_leibnizW hu,
    tsupport_leibnizW_subset_closedBall _, fun ℓ => ⟨contDiff_leibnizG hV ℓ,
    tsupport_leibnizG_subset ℓ⟩, contDiff_leibnizH hμ hu hV, tsupport_leibnizH_subset,
    hid, fun x => ?_⟩
  have hf : (fun y => matVecMul (ellipticMatrix A P₀)
        (classicalGradient (leibnizW (mollU x₀ r c ε σ)) y)) =
      fun y => (∑ ℓ, fun i =>
            euclideanCoordDeriv ℓ (fun z => leibnizG A P₀ (mollV x₀ r c ε σ P P₀) ℓ z i) y) +
          leibnizH A A₀ P₀ r (mollMu x₀ r c ε σ P) (mollU x₀ r c ε σ)
            (mollV x₀ r c ε σ P P₀) y := funext hid
  rw [hf]

/-- Quantitative part: the `L¹` bounds
`Σ_ℓ ‖G^{(ℓ)}‖_{L¹} ≤ K_G δ(r)` and `‖H‖_{L¹} ≤ K_H (1 + |P₀| + δ(r))`, with `K_G`, `K_H`
depending only on `A`, `A₀`, `P₀` and the fixed cut-off `χ` (not on `σ`, `P`, `x₀`, `r`, `ε`).
Hypotheses: `0 < r ≤ 1` (the paper uses `r_j ≤ 1`), `0 < σˢ(Q_r(x₀)) < ∞` (so `ν_r(Q₁) = 1`),
`P₀ = P(x₀)` (the normalisation used in the definition of `δ(r)`), `σ` finite, `P ∈ L¹(σ)`, `ε ∈ (0,1/8]`. -/
theorem leibniz_bounds (A : Fin d → Matrix (Fin n) (Fin m) ℝ) (A₀ : Matrix (Fin n) (Fin m) ℝ)
    (P₀ : Vec m) :
    ∃ K_G K_H : ℝ, 0 ≤ K_G ∧ 0 ≤ K_H ∧
      ∀ (σ : Measure (Vec d)) [IsFiniteMeasure σ] (P : Vec d → Vec m) (x₀ : Vec d),
        P x₀ = P₀ → Integrable P σ → ∀ {r : ℝ}, 0 < r → r ≤ 1 →
        0 < σ.singularPart volume (Metric.closedBall x₀ r) →
        σ.singularPart volume (Metric.closedBall x₀ r) < ∞ →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 8 →
        (∑ ℓ, ∫ x, vecEuclideanNorm
          (leibnizG A P₀ (mollV x₀ r (blowConst σ x₀ r) ε σ P P₀) ℓ x)) ≤
            K_G * blowDelta σ x₀ P r ∧
        ∫ x, vecEuclideanNorm (leibnizH A A₀ P₀ r (mollMu x₀ r (blowConst σ x₀ r) ε σ P)
          (mollU x₀ r (blowConst σ x₀ r) ε σ) (mollV x₀ r (blowConst σ x₀ r) ε σ P P₀) x) ≤
            K_H * (1 + vecEuclideanNorm P₀ + blowDelta σ x₀ P r) := by
  obtain ⟨C, hC0, hC⟩ := exists_gradient_cutoff_bound (d := d)
  set mBT := matBound (symbolColumns A P₀)ᵀ with hmBT
  set mB := matBound (symbolColumns A P₀) with hmB
  set mA := ∑ ℓ, matBound (A ℓ) with hmA
  set mA0 := matBound A₀ with hmA0
  have hmBT0 : 0 ≤ mBT := matBound_nonneg _
  have hmB0 : 0 ≤ mB := matBound_nonneg _
  have hmA0' : 0 ≤ mA := Finset.sum_nonneg fun ℓ _ => matBound_nonneg _
  have hmA00 : 0 ≤ mA0 := matBound_nonneg _
  refine ⟨mBT * mA, mBT * (C * mA + mA0 + mB * C), by positivity, by positivity, ?_⟩
  intro σ _ P x₀ hP₀ hP r hr hr1 hpos hfin ε hε hε8
  subst hP₀
  have hc := blowConst_ne_top hpos
  set c := blowConst σ x₀ r with hcdef
  have hμ := contDiff_mollMu hr hc hP hε (x₀ := x₀)
  have hu := contDiff_mollU hc hε (σ := σ) (x₀ := x₀) (r := r)
  have hV := contDiff_mollV hr hc hP hε (P x₀) (x₀ := x₀)
  have hδ : 0 ≤ blowDelta σ x₀ P r := by
    unfold blowDelta
    exact add_nonneg (integral_nonneg fun _ => vecEuclideanNorm_nonneg _)
      (integral_nonneg fun _ => vecEuclideanNorm_nonneg _)
  have hVb := integral_mollV_le hr hpos hP hε hε8
  have hMb := integral_mollMu_le hr hpos hfin hP hε hε8
  have hUb := integral_mollU_le_one hr hpos hfin hε hε8 (σ := σ)
  set B := euclideanBall (0 : Vec d) (7 / 8) with hBdef
  have hVi : IntegrableOn (fun x => vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x)) B :=
    integrableOn_euclideanBall_of_continuous
      (continuous_vecEuclideanNorm.comp hV.continuous) (by norm_num) (by norm_num)
  have hMi : IntegrableOn (fun x => vecEuclideanNorm (mollMu x₀ r c ε σ P x)) B :=
    integrableOn_euclideanBall_of_continuous
      (continuous_vecEuclideanNorm.comp hμ.continuous) (by norm_num) (by norm_num)
  have hUi : IntegrableOn (fun x => mollU x₀ r c ε σ x) B :=
    integrableOn_euclideanBall_of_continuous hu.continuous (by norm_num) (by norm_num)
  have hχzero : ∀ x ∉ B, euclideanCutoff (1 / 2 : ℝ) (3 / 4) x = 0 := fun x hx =>
    cutoff_eq_zero_of_notMem (notMem_tsupport_cutoff_of_notMem hx)
  have hGzero : ∀ ℓ, ∀ x ∉ B,
      vecEuclideanNorm (leibnizG A (P x₀) (mollV x₀ r c ε σ P (P x₀)) ℓ x) = 0 := by
    intro ℓ x hx
    refine vecEuclideanNorm_eq_zero_iff.2 ?_
    unfold leibnizG
    rw [hχzero x hx, zero_smul, Matrix.mulVec_zero, Matrix.mulVec_zero, neg_zero]
  have hHzero : ∀ x ∉ B,
      vecEuclideanNorm (leibnizH A A₀ (P x₀) r (mollMu x₀ r c ε σ P) (mollU x₀ r c ε σ)
        (mollV x₀ r c ε σ P (P x₀)) x) = 0 := fun x hx =>
    vecEuclideanNorm_eq_zero_iff.2 (leibnizH_eq_zero_of_notMem (notMem_tsupport_cutoff_of_notMem hx))
  have hGl : ∀ ℓ, ∫ x, vecEuclideanNorm (leibnizG A (P x₀) (mollV x₀ r c ε σ P (P x₀)) ℓ x) ≤
      (mBT * matBound (A ℓ)) * blowDelta σ x₀ P r := by
    intro ℓ
    have hGi : IntegrableOn (fun x => vecEuclideanNorm
        (leibnizG A (P x₀) (mollV x₀ r c ε σ P (P x₀)) ℓ x)) B :=
      integrableOn_euclideanBall_of_continuous (continuous_vecEuclideanNorm.comp
        (contDiff_leibnizG hV ℓ).continuous) (by norm_num) (by norm_num)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) (hGzero ℓ)]
    calc _ ≤ ∫ x in B, (mBT * matBound (A ℓ)) *
          vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x) :=
          setIntegral_mono hGi (hVi.const_mul _) fun x => norm_leibnizG_le ℓ x
      _ = (mBT * matBound (A ℓ)) *
          (∫ x in B, vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x)) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hVb (mul_nonneg hmBT0 (matBound_nonneg _))
  refine ⟨?_, ?_⟩
  · calc _ ≤ ∑ ℓ, (mBT * matBound (A ℓ)) * blowDelta σ x₀ P r := Finset.sum_le_sum fun ℓ _ => hGl ℓ
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  · have hHi : IntegrableOn (fun x => vecEuclideanNorm
        (leibnizH A A₀ (P x₀) r (mollMu x₀ r c ε σ P) (mollU x₀ r c ε σ)
          (mollV x₀ r c ε σ P (P x₀)) x)) B :=
      integrableOn_euclideanBall_of_continuous (continuous_vecEuclideanNorm.comp
        (contDiff_leibnizH hμ hu hV).continuous) (by norm_num) (by norm_num)
    have hI : IntegrableOn (fun x => mBT * ((C * mA) *
        vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x) +
        mA0 * vecEuclideanNorm (mollMu x₀ r c ε σ P x) + (mB * C) * mollU x₀ r c ε σ x)) B :=
      (((hVi.const_mul _).add (hMi.const_mul _)).add (hUi.const_mul _)).const_mul _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) hHzero]
    calc _ ≤ ∫ x in B, mBT * ((C * mA) * vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x) +
          mA0 * vecEuclideanNorm (mollMu x₀ r c ε σ P x) + (mB * C) * mollU x₀ r c ε σ x) := by
          refine setIntegral_mono hHi hI fun x => ?_
          refine (norm_leibnizH_le x).trans (mul_le_mul_of_nonneg_left ?_ hmBT0)
          exact norm_leibnizR_le hC hr.le hr1 (mollU_nonneg hε.le σ) x
      _ = mBT * ((C * mA) * (∫ x in B, vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x)) +
          mA0 * (∫ x in B, vecEuclideanNorm (mollMu x₀ r c ε σ P x)) +
          (mB * C) * (∫ x in B, mollU x₀ r c ε σ x)) := by
          have hs1 : Integrable (fun x => (C * mA) * vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x) +
              mA0 * vecEuclideanNorm (mollMu x₀ r c ε σ P x)) (volume.restrict B) :=
            (hVi.const_mul _).add (hMi.const_mul _)
          have hs2 : Integrable (fun x => (C * mA) * vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x))
              (volume.restrict B) := hVi.const_mul _
          have hs3 : Integrable (fun x => mA0 * vecEuclideanNorm (mollMu x₀ r c ε σ P x))
              (volume.restrict B) := hMi.const_mul _
          have hs4 : Integrable (fun x => (mB * C) * mollU x₀ r c ε σ x)
              (volume.restrict B) := hUi.const_mul _
          rw [integral_const_mul, integral_add hs1 hs4, integral_add hs2 hs3,
            integral_const_mul, integral_const_mul, integral_const_mul]
      _ ≤ _ := by
          have hn := vecEuclideanNorm_nonneg (P x₀)
          have h1 : (C * mA) * (∫ x in B, vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x)) ≤
              (C * mA) * blowDelta σ x₀ P r := mul_le_mul_of_nonneg_left hVb (by positivity)
          have h2 : mA0 * (∫ x in B, vecEuclideanNorm (mollMu x₀ r c ε σ P x)) ≤
              mA0 * (vecEuclideanNorm (P x₀) + blowDelta σ x₀ P r) :=
            mul_le_mul_of_nonneg_left hMb hmA00
          have h3 : (mB * C) * (∫ x in B, mollU x₀ r c ε σ x) ≤ (mB * C) * 1 :=
            mul_le_mul_of_nonneg_left hUb (by positivity)
          have key : (C * mA) * blowDelta σ x₀ P r + mA0 * (vecEuclideanNorm (P x₀) +
              blowDelta σ x₀ P r) + (mB * C) * 1 ≤
              (C * mA + mA0 + mB * C) * (1 + vecEuclideanNorm (P x₀) + blowDelta σ x₀ P r) := by
            have e1 : 0 ≤ C * mA := by positivity
            have e3 : 0 ≤ mB * C := by positivity
            nlinarith [mul_nonneg e1 hn, mul_nonneg e3 hn, mul_nonneg e3 hδ, mul_nonneg hmA00 hn]
          calc _ ≤ mBT * ((C * mA) * blowDelta σ x₀ P r + mA0 * (vecEuclideanNorm (P x₀) +
              blowDelta σ x₀ P r) + (mB * C) * 1) :=
                mul_le_mul_of_nonneg_left (by linarith) hmBT0
            _ ≤ mBT * ((C * mA + mA0 + mB * C) *
                (1 + vecEuclideanNorm (P x₀) + blowDelta σ x₀ P r)) :=
                mul_le_mul_of_nonneg_left key hmBT0
            _ = _ := by ring

end AFree
