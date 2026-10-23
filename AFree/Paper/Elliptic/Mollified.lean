module

public import AFree.Paper.BlowUp
public import AFree.Measure.Mollify
public import AFree.Paper.Elliptic.Calculus
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# The mollified equation and smallness

The mollified equation and the `L¹` bounds on the mollified blow-ups, for a single radius
`r ∈ (0,1]` and a single scale `ε ∈ (0,1/8]` ([DPR, proof of Theorem 1.1]).
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal

namespace AFree

open PDE

variable {d : ℕ} {σ : Measure (Vec d)}

section Setup

lemma isFiniteMeasure_blowMeasure (x₀ : Vec d) (r : ℝ) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (τ : Measure (Vec d)) [IsFiniteMeasure τ] : IsFiniteMeasure (blowMeasure x₀ r c τ) := by
  unfold blowMeasure
  have : IsFiniteMeasure (τ.map (blowMap x₀ r)) := Measure.isFiniteMeasure_map _ _
  exact Measure.smul_finite _ hc

lemma blowMeasure_mono (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) {τ τ' : Measure (Vec d)} (h : τ ≤ τ') :
    blowMeasure x₀ r c τ ≤ blowMeasure x₀ r c τ' := by
  unfold blowMeasure
  intro s
  rw [Measure.smul_apply, Measure.smul_apply]
  exact smul_le_smul_of_nonneg_left (Measure.map_mono h (measurable_blowMap x₀ r) s) zero_le

lemma integrable_blowDensity {ι : Type*} [Fintype ι] (x₀ : Vec d) {r : ℝ} (hr : r ≠ 0)
    {c : ℝ≥0∞} (hc : c ≠ ∞) {τ : Measure (Vec d)} {P : Vec d → ι → ℝ} (hP : Integrable P τ) :
    Integrable (blowDensity x₀ r P) (blowMeasure x₀ r c τ) := by
  unfold blowMeasure
  refine Integrable.smul_measure ?_ hc
  rw [(measurableEmbedding_blowMap x₀ hr).integrable_map_iff]
  have : blowDensity x₀ r P ∘ blowMap x₀ r = P := funext (blowDensity_blowMap x₀ hr P)
  rwa [this]

/-- The thickening `(B_{7/8})^ε` lies in `B₁` for `ε ≤ 1/8`. -/
lemma thickening_subset {ε : ℝ} (hεpos : 0 < ε) (hε : ε ≤ 1 / 8) :
    {y : Vec d | ∃ x ∈ euclideanBall (0 : Vec d) (7 / 8), x ∈ euclideanBall y ε} ⊆
      euclideanBall 0 1 := by
  rintro y ⟨x, hx, hxy⟩
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)] at hx
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hεpos] at hxy
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
  have : y - 0 = x - 0 - (x - y) := by simp
  rw [this]
  have h2 := vecEuclideanNorm_add_le (x - 0) (-(x - y))
  rw [vecEuclideanNorm_neg, ← sub_eq_add_neg] at h2
  linarith

lemma integrableOn_euclideanBall_of_continuous {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    (hf : Continuous f) {a : ℝ} (ha : a ≤ 1) (ha0 : 0 ≤ a) :
    IntegrableOn f (euclideanBall (0 : Vec d) a) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Vec d) 1)).mono_set
    ((euclideanBall_zero_mono ha0 ha).trans euclideanBall_one_subset_closedBall_one)

end Setup

section MollPDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- The mollified equation: for `x ∈ B_{7/8}`,
`Σ_ℓ A_ℓ ∂_ℓ μ^ε(x) + r A₀ μ^ε(x) = 0`, with `μ^ε = (P_r σ_r)_ε`.
Hypotheses: `(σ,P)` is `𝒜`-free in `Ω`,
`Q_r(x₀) ⊆ Ω`, `ε ∈ (0,1/8]`, `P ∈ L¹(σ)`, and `c < ∞` (the constant
`c = σˢ(Q_r(x₀))⁻¹` of the construction is finite). -/
theorem mollified_equation {Ω : Set (Vec d)} {A : Fin d → Matrix κ ι ℝ} {A₀ : Matrix κ ι ℝ}
    {σ : Measure (Vec d)} {P : Vec d → ι → ℝ} (h : IsFreePair Ω A A₀ σ P) (x₀ : Vec d)
    {r : ℝ} (hr : 0 < r) (hΩ : Metric.closedBall x₀ r ⊆ Ω) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) (7 / 8)) :
    (∑ ℓ, A ℓ *ᵥ fderiv ℝ (mollify ε (blowMeasure x₀ r c σ) (blowDensity x₀ r P)) x (basisVec ℓ)) +
      r • (A₀ *ᵥ mollify ε (blowMeasure x₀ r c σ) (blowDensity x₀ r P) x) = 0 := by
  set ψ : Vec d → ℝ := fun y => scaledMollifier ε (x - y) with hψdef
  have hψ : IsTestFunctionOn (blowMap x₀ r '' Ω) ψ := by
    refine ⟨(contDiff_scaledMollifier ε).comp (contDiff_const.sub contDiff_id), ?_, ?_⟩
    · exact (hasCompactSupport_scaledMollifier hε).comp_homeomorph (Homeomorph.subLeft x)
    · have h1 : tsupport ψ = (fun y => x - y) ⁻¹' tsupport (scaledMollifier (d := d) ε) :=
        tsupport_comp_eq_preimage (scaledMollifier (d := d) ε) (Homeomorph.subLeft x)
      rw [h1]
      refine Subset.trans ?_ (closedBall_one_subset_blowMap_image x₀ hr hΩ)
      refine Subset.trans ?_ euclideanBall_one_subset_closedBall_one
      intro y hy
      have hy' := tsupport_scaledMollifier_subset hε hy
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hε, sub_zero] at hy'
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)] at hx
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num), sub_zero]
      have h2 := vecEuclideanNorm_add_le x (-(x - y))
      rw [vecEuclideanNorm_neg, ← sub_eq_add_neg, sub_sub_cancel] at h2
      rw [sub_zero] at hx
      linarith
  have key := blowUp_equation h x₀ hr c hψ
  have hint := integrable_blowDensity x₀ hr.ne' hc hP (τ := σ) (c := c)
  have hfd : ∀ z ℓ, euclideanCoordDeriv ℓ ψ z =
      -fderiv ℝ (scaledMollifier (d := d) ε) (x - z) (basisVec ℓ) := by
    intro z ℓ
    have hd : DifferentiableAt ℝ (scaledMollifier (d := d) ε) (x - z) :=
      ((contDiff_scaledMollifier ε).differentiable (by simp)) _
    have := hd.hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub x)
    unfold euclideanCoordDeriv
    have e : ψ = (scaledMollifier (d := d) ε) ∘ fun y => x - y := rfl
    rw [e, this.fderiv]
    simp
  have e1 : ∀ ℓ, ∫ z, euclideanCoordDeriv ℓ ψ z • blowDensity x₀ r P z ∂blowMeasure x₀ r c σ =
      -fderiv ℝ (mollify ε (blowMeasure x₀ r c σ) (blowDensity x₀ r P)) x (basisVec ℓ) := by
    intro ℓ
    rw [fderiv_mollify hε _ hint, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hfd, neg_smul]
  have e0 : ∫ z, ψ z • blowDensity x₀ r P z ∂blowMeasure x₀ r c σ =
      mollify ε (blowMeasure x₀ r c σ) (blowDensity x₀ r P) x := rfl
  rw [e0] at key
  simp only [e1, Matrix.mulVec_neg, Finset.sum_neg_distrib] at key
  rw [key]
  simp

end MollPDE

section Small

variable {m : ℕ}

/-- `μ^ε = (P_r σ_r)_ε`, for a given scale `ε` and constant `c`. -/
noncomputable def mollMu (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) (ε : ℝ) (σ : Measure (Vec d))
    (P : Vec d → Vec m) : Vec d → Vec m :=
  mollify ε (blowMeasure x₀ r c σ) (blowDensity x₀ r P)

/-- `u = (ν_r)_ε`, the mollification of the singular blow-up. -/
noncomputable def mollU (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) (ε : ℝ) (σ : Measure (Vec d)) :
    Vec d → ℝ :=
  mollifyMeasure ε (blowMeasure x₀ r c (σ.singularPart volume))

/-- `V = μ^ε − u P₀`. -/
noncomputable def mollV (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) (ε : ℝ) (σ : Measure (Vec d))
    (P : Vec d → Vec m) (P₀ : Vec m) : Vec d → Vec m :=
  fun x => mollMu x₀ r c ε σ P x - mollU x₀ r c ε σ x • P₀

lemma integrable_vecEuclideanNorm_of_integrable {k : ℕ} {τ : Measure (Vec d)} {f : Vec d → Vec k}
    (hf : Integrable f τ) : Integrable (fun y => vecEuclideanNorm (f y)) τ :=
  integrable_vecEuclideanNorm_of_coord f fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).integrable_comp hf

lemma continuous_vecEuclideanNorm {k : ℕ} : Continuous (fun v : Vec k => vecEuclideanNorm v) := by
  unfold vecEuclideanNorm vecNormSq vecDot
  fun_prop

lemma contDiff_mollMu [IsFiniteMeasure σ] {x₀ : Vec d} {r : ℝ} (hr : 0 < r) {c : ℝ≥0∞}
    (hc : c ≠ ∞) {P : Vec d → Vec m} (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (mollMu x₀ r c ε σ P) :=
  contDiff_mollify hε _ (integrable_blowDensity x₀ hr.ne' hc hP)

lemma contDiff_mollU {x₀ : Vec d} {r : ℝ} {c : ℝ≥0∞} (hc : c ≠ ∞) {σ : Measure (Vec d)}
    [IsFiniteMeasure σ] {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (mollU x₀ r c ε σ) := by
  have : IsFiniteMeasure (σ.singularPart volume) :=
    isFiniteMeasure_of_le σ (Measure.singularPart_le σ volume)
  have := isFiniteMeasure_blowMeasure x₀ r hc (σ.singularPart volume)
  exact contDiff_mollify hε _ (integrable_const (1 : ℝ))

lemma mollU_nonneg {x₀ : Vec d} {r : ℝ} {c : ℝ≥0∞} {ε : ℝ} (hε : 0 ≤ ε) (σ : Measure (Vec d))
    (x : Vec d) : 0 ≤ mollU x₀ r c ε σ x :=
  mollifyMeasure_nonneg hε _ x

lemma contDiff_mollV [IsFiniteMeasure σ] {x₀ : Vec d} {r : ℝ} (hr : 0 < r) {c : ℝ≥0∞}
    (hc : c ≠ ∞) {P : Vec d → Vec m} (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε) (P₀ : Vec m) :
    ContDiff ℝ (⊤ : ℕ∞) (mollV x₀ r c ε σ P P₀) :=
  (contDiff_mollMu hr hc hP hε).sub ((contDiff_mollU hc hε).smul contDiff_const)

variable [IsFiniteMeasure σ]

lemma mollV_eq {x₀ : Vec d} {r : ℝ} (hr : 0 < r) {c : ℝ≥0∞} (hc : c ≠ ∞) {P : Vec d → Vec m}
    (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε) (P₀ : Vec m) (x : Vec d) :
    mollV x₀ r c ε σ P P₀ x =
      mollify ε (blowMeasure x₀ r c (volume.withDensity (σ.rnDeriv volume))) (blowDensity x₀ r P) x +
      mollify ε (blowMeasure x₀ r c (σ.singularPart volume))
        (fun y => blowDensity x₀ r P y - P₀) x := by
  have hint := integrable_blowDensity x₀ hr.ne' hc hP (c := c)
  have hα : blowMeasure x₀ r c (volume.withDensity (σ.rnDeriv volume)) ≤ blowMeasure x₀ r c σ :=
    blowMeasure_mono x₀ r c (Measure.withDensity_rnDeriv_le σ volume)
  have hν : blowMeasure x₀ r c (σ.singularPart volume) ≤ blowMeasure x₀ r c σ :=
    blowMeasure_mono x₀ r c (Measure.singularPart_le σ volume)
  have hΦ := (contDiff_scaledMollifier (d := d) ε).continuous
  have hc' := hasCompactSupport_scaledMollifier (d := d) hε
  have k1 := integrable_kernel hΦ hc' (hint.mono_measure hα) x
  have k2 := integrable_kernel hΦ hc' (hint.mono_measure hν) x
  have k3 : Integrable (fun y => scaledMollifier ε (x - y) • P₀)
      (blowMeasure x₀ r c (σ.singularPart volume)) := by
    have := integrable_kernel hΦ hc' (E := Vec m) (τ := blowMeasure x₀ r c (σ.singularPart volume))
      (f := fun _ => P₀) (by
        have : IsFiniteMeasure (σ.singularPart volume) :=
          isFiniteMeasure_of_le σ (Measure.singularPart_le σ volume)
        have := isFiniteMeasure_blowMeasure x₀ r hc (σ.singularPart volume)
        exact integrable_const _) x
    exact this
  have hsplit : mollify ε (blowMeasure x₀ r c σ) (blowDensity x₀ r P) x =
      mollify ε (blowMeasure x₀ r c (volume.withDensity (σ.rnDeriv volume))) (blowDensity x₀ r P) x +
      mollify ε (blowMeasure x₀ r c (σ.singularPart volume)) (blowDensity x₀ r P) x := by
    unfold mollify
    rw [blowMeasure_eq_add x₀ r c σ, integral_add_measure k1 k2]
  have hu : mollU x₀ r c ε σ x • P₀ =
      ∫ y, scaledMollifier ε (x - y) • P₀ ∂blowMeasure x₀ r c (σ.singularPart volume) := by
    unfold mollU mollifyMeasure mollify
    rw [← integral_smul_const]
    simp
  unfold mollV mollMu
  rw [hsplit, hu]
  unfold mollify
  simp only [smul_sub]
  rw [integral_sub k2 k3]
  abel

end Small

section SmallThm

variable {m : ℕ}

variable [IsFiniteMeasure σ]

omit [IsFiniteMeasure σ] in
lemma blowConst_ne_top {x₀ : Vec d} {r : ℝ}
    (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r)) : blowConst σ x₀ r ≠ ∞ :=
  ENNReal.inv_ne_top.2 hpos.ne'

/-- `∫_{B_{7/8}} u ≤ 1`. -/
theorem integral_mollU_le_one {x₀ : Vec d} {r : ℝ} (hr : 0 < r)
    (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r))
    (hfin : σ.singularPart volume (Metric.closedBall x₀ r) < ∞) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) :
    ∫ x in euclideanBall (0 : Vec d) (7 / 8), mollU x₀ r (blowConst σ x₀ r) ε σ x ≤ 1 := by
  have hc := blowConst_ne_top hpos
  have : IsFiniteMeasure (σ.singularPart volume) :=
    isFiniteMeasure_of_le σ (Measure.singularPart_le σ volume)
  have := isFiniteMeasure_blowMeasure x₀ r hc (σ.singularPart volume)
  set ν := blowMeasure x₀ r (blowConst σ x₀ r) (σ.singularPart volume) with hν
  have h1 := integral_norm_mollify_le hε ν (f := fun _ => (1 : ℝ)) (integrable_const 1)
    (measurableSet_euclideanBall (0 : Vec d) (7 / 8))
  have hL : ∫ x in euclideanBall (0 : Vec d) (7 / 8), mollU x₀ r (blowConst σ x₀ r) ε σ x =
      ∫ x in euclideanBall (0 : Vec d) (7 / 8), ‖mollify ε ν (fun _ => (1 : ℝ)) x‖ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := mollU_nonneg (x₀ := x₀) (r := r) (c := blowConst σ x₀ r) hε.le σ x
    show _ = ‖mollifyMeasure ε ν x‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by exact this)]
    rfl
  rw [hL]
  refine h1.trans ?_
  have hS : MeasurableSet {y : Vec d | ∃ x ∈ euclideanBall (0 : Vec d) (7 / 8), x ∈ euclideanBall y ε} :=
    (isOpen_thickening _ _).measurableSet
  have h2 : ν {y : Vec d | ∃ x ∈ euclideanBall (0 : Vec d) (7 / 8), x ∈ euclideanBall y ε} ≤ 1 := by
    calc _ ≤ ν (Metric.closedBall 0 1) :=
          measure_mono ((thickening_subset hε hε8).trans euclideanBall_one_subset_closedBall_one)
      _ = 1 := blowMeasure_closedBall_one x₀ r σ hr hpos hfin
  simp only [norm_one, integral_const, smul_eq_mul, mul_one, Measure.restrict_apply_univ,
    Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h2)

/-- `∫_{B_{7/8}} |V| ≤ δ(r)`, with `P₀ = P(x₀)`. -/
theorem integral_mollV_le {x₀ : Vec d} {r : ℝ} (hr : 0 < r)
    (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r))
    {P : Vec d → Vec m} (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∫ x in euclideanBall (0 : Vec d) (7 / 8),
        vecEuclideanNorm (mollV x₀ r (blowConst σ x₀ r) ε σ P (P x₀) x) ≤
      blowDelta σ x₀ P r := by
  have hc := blowConst_ne_top hpos
  set c := blowConst σ x₀ r with hcdef
  have hfs : IsFiniteMeasure (σ.singularPart volume) :=
    isFiniteMeasure_of_le σ (Measure.singularPart_le σ volume)
  have hfa : IsFiniteMeasure (volume.withDensity (σ.rnDeriv volume)) :=
    isFiniteMeasure_of_le σ (Measure.withDensity_rnDeriv_le σ volume)
  have hνf := isFiniteMeasure_blowMeasure x₀ r hc (σ.singularPart volume)
  have hαf := isFiniteMeasure_blowMeasure x₀ r hc (volume.withDensity (σ.rnDeriv volume))
  set α := blowMeasure x₀ r c (volume.withDensity (σ.rnDeriv volume)) with hα
  set ν := blowMeasure x₀ r c (σ.singularPart volume) with hν
  have hint := integrable_blowDensity x₀ hr.ne' hc hP (c := c)
  have hintα : Integrable (blowDensity x₀ r P) α :=
    hint.mono_measure (blowMeasure_mono x₀ r c (Measure.withDensity_rnDeriv_le σ volume))
  have hintν : Integrable (blowDensity x₀ r P) ν :=
    hint.mono_measure (blowMeasure_mono x₀ r c (Measure.singularPart_le σ volume))
  have hintν' : Integrable (fun y => blowDensity x₀ r P y - P x₀) ν :=
    hintν.sub (integrable_const _)
  have hB : MeasurableSet (euclideanBall (0 : Vec d) (7 / 8)) := measurableSet_euclideanBall _ _
  set B := euclideanBall (0 : Vec d) (7 / 8) with hBdef
  have ha := contDiff_mollify hε α hintα
  have hb := contDiff_mollify hε ν hintν'
  have hna : IntegrableOn (fun x => vecEuclideanNorm (mollify ε α (blowDensity x₀ r P) x)) B :=
    integrableOn_euclideanBall_of_continuous (continuous_vecEuclideanNorm.comp ha.continuous)
      (by norm_num) (by norm_num)
  have hnb : IntegrableOn
      (fun x => vecEuclideanNorm (mollify ε ν (fun y => blowDensity x₀ r P y - P x₀) x)) B :=
    integrableOn_euclideanBall_of_continuous (continuous_vecEuclideanNorm.comp hb.continuous)
      (by norm_num) (by norm_num)
  have hstep : ∀ x, vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x) ≤
      vecEuclideanNorm (mollify ε α (blowDensity x₀ r P) x) +
      vecEuclideanNorm (mollify ε ν (fun y => blowDensity x₀ r P y - P x₀) x) := by
    intro x
    rw [mollV_eq hr hc hP hε]
    exact vecEuclideanNorm_add_le _ _
  have hV : IntegrableOn (fun x => vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x)) B :=
    integrableOn_euclideanBall_of_continuous (continuous_vecEuclideanNorm.comp
      (contDiff_mollV hr hc hP hε _).continuous) (by norm_num) (by norm_num)
  have h1 := integral_vecEuclideanNorm_mollify_le hε α hintα hB
  have h2 := integral_vecEuclideanNorm_mollify_le hε ν hintν' hB
  have hsub : {y : Vec d | ∃ x ∈ B, x ∈ euclideanBall y ε} ⊆ Metric.closedBall 0 1 :=
    Set.Subset.trans (thickening_subset hε hε8) euclideanBall_one_subset_closedBall_one
  have m1 : ∫ y in {y : Vec d | ∃ x ∈ B, x ∈ euclideanBall y ε}, vecEuclideanNorm (blowDensity x₀ r P y) ∂α ≤
      ∫ y in Metric.closedBall 0 1, vecEuclideanNorm (blowDensity x₀ r P y) ∂α :=
    setIntegral_mono_set (integrable_vecEuclideanNorm_of_integrable hintα).integrableOn
      (Eventually.of_forall fun _ => vecEuclideanNorm_nonneg _) hsub.eventuallyLE
  have m2 : ∫ y in {y : Vec d | ∃ x ∈ B, x ∈ euclideanBall y ε},
        vecEuclideanNorm (blowDensity x₀ r P y - P x₀) ∂ν ≤
      ∫ y in Metric.closedBall 0 1, vecEuclideanNorm (blowDensity x₀ r P y - P x₀) ∂ν :=
    setIntegral_mono_set (integrable_vecEuclideanNorm_of_integrable hintν').integrableOn
      (Eventually.of_forall fun _ => vecEuclideanNorm_nonneg _) hsub.eventuallyLE
  calc _ ≤ ∫ x in B, (vecEuclideanNorm (mollify ε α (blowDensity x₀ r P) x) +
        vecEuclideanNorm (mollify ε ν (fun y => blowDensity x₀ r P y - P x₀) x)) :=
        setIntegral_mono hV (hna.add hnb) hstep
    _ = _ := integral_add hna hnb
    _ ≤ _ := by
        unfold blowDelta
        exact add_le_add (h1.trans m1) (h2.trans m2)

/-- `∫_{B_{7/8}} |μ^ε| ≤ |P₀| + δ(r)`, with `P₀ = P(x₀)`. -/
theorem integral_mollMu_le {x₀ : Vec d} {r : ℝ} (hr : 0 < r)
    (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r))
    (hfin : σ.singularPart volume (Metric.closedBall x₀ r) < ∞)
    {P : Vec d → Vec m} (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∫ x in euclideanBall (0 : Vec d) (7 / 8),
        vecEuclideanNorm (mollMu x₀ r (blowConst σ x₀ r) ε σ P x) ≤
      vecEuclideanNorm (P x₀) + blowDelta σ x₀ P r := by
  have hc := blowConst_ne_top hpos
  set c := blowConst σ x₀ r with hcdef
  have hu := integral_mollU_le_one hr hpos hfin hε hε8 (σ := σ)
  have hv := integral_mollV_le hr hpos hP hε hε8
  have hstep : ∀ x, vecEuclideanNorm (mollMu x₀ r c ε σ P x) ≤
      vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x) +
        vecEuclideanNorm (P x₀) * mollU x₀ r c ε σ x := by
    intro x
    have : mollMu x₀ r c ε σ P x = mollV x₀ r c ε σ P (P x₀) x + mollU x₀ r c ε σ x • P x₀ := by
      simp [mollV]
    rw [this]
    refine (vecEuclideanNorm_add_le _ _).trans ?_
    rw [vecEuclideanNorm_smul, abs_of_nonneg (mollU_nonneg hε.le σ x), mul_comm]
  have hVi : IntegrableOn (fun x => vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x))
      (euclideanBall (0 : Vec d) (7 / 8)) :=
    integrableOn_euclideanBall_of_continuous (continuous_vecEuclideanNorm.comp
      (contDiff_mollV hr hc hP hε _).continuous) (by norm_num) (by norm_num)
  have hUi : IntegrableOn (fun x => vecEuclideanNorm (P x₀) * mollU x₀ r c ε σ x)
      (euclideanBall (0 : Vec d) (7 / 8)) :=
    (integrableOn_euclideanBall_of_continuous (contDiff_mollU hc hε (σ := σ)
      (x₀ := x₀) (r := r)).continuous (by norm_num) (by norm_num)).const_mul _
  have hMi : IntegrableOn (fun x => vecEuclideanNorm (mollMu x₀ r c ε σ P x))
      (euclideanBall (0 : Vec d) (7 / 8)) :=
    integrableOn_euclideanBall_of_continuous (continuous_vecEuclideanNorm.comp
      (contDiff_mollMu hr hc hP hε).continuous) (by norm_num) (by norm_num)
  calc _ ≤ ∫ x in euclideanBall (0 : Vec d) (7 / 8), (vecEuclideanNorm (mollV x₀ r c ε σ P (P x₀) x) +
        vecEuclideanNorm (P x₀) * mollU x₀ r c ε σ x) := setIntegral_mono hMi (hVi.add hUi) hstep
    _ = _ := integral_add hVi hUi
    _ ≤ _ := by
        rw [integral_const_mul]
        have := mul_le_mul_of_nonneg_left hu (vecEuclideanNorm_nonneg (P x₀))
        linarith

end SmallThm

end AFree
