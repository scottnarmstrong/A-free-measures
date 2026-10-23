module

public import AFree.Paper.OrderK.BlowUpMollvar
public import AFree.Measure.Concentration

/-!
# Scale of mollification and smallness

The mollification scale and the smallness of the mollified blow-ups, with general finite carriers
`ι` (Euclidean norm `piEuclideanNorm`) in place of `Fin m`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix PDE
open scoped ENNReal

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `μ^ε = (P_r σ_r)_ε`, with values in `ℝ^ι`. -/
def mollMuK (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) (ε : ℝ) (σ : Measure (Vec d)) (P : Vec d → ι → ℝ) :
    Vec d → ι → ℝ :=
  mollify ε (blowMeasure x₀ r c σ) (blowDensity x₀ r P)

/-- `V = μ^ε - u P₀`, with values in `ℝ^ι`. -/
def mollVK (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) (ε : ℝ) (σ : Measure (Vec d)) (P : Vec d → ι → ℝ)
    (P0 : ι → ℝ) : Vec d → ι → ℝ :=
  fun x => mollMuK x₀ r c ε σ P x - mollU x₀ r c ε σ x • P0

theorem mollMuK_eq (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) (ε : ℝ) (σ : Measure (Vec d))
    (P : Vec d → ι → ℝ) (P0 : ι → ℝ) (x : Vec d) :
    mollMuK x₀ r c ε σ P x = mollU x₀ r c ε σ x • P0 + mollVK x₀ r c ε σ P P0 x := by
  simp [mollVK]

/-- The concentration step: there are an open `W ⊆ B_{1/2}` with `|W| < η` and `ε₀ > 0`
such that `t^{d+1} ≤ ∫_W u + η` for all `ε ∈ (0, ε₀]`, where `u = (ν_r)_ε`. -/
theorem exists_epsK (hd : 0 < d) (σ : Measure (Vec d)) [IsFiniteMeasure σ] (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r))
    (hG4 : ENNReal.ofReal (badT d ^ (d + 1)) * σ.singularPart volume (Metric.closedBall x₀ r) ≤
      σ.singularPart volume (Metric.closedBall x₀ (badT d * r))) {η : ℝ} (hη : 0 < η) :
    ∃ W : Set (Vec d), IsOpen W ∧ W ⊆ euclideanBall (0 : Vec d) (1 / 2) ∧
      volume W < ENNReal.ofReal η ∧ ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀,
        badT d ^ (d + 1) ≤ (∫ x in W, mollU x₀ r (blowConst σ x₀ r) ε σ x) + η := by
  have hc := blowConst_ne_top hpos
  have hfs : IsFiniteMeasure (σ.singularPart volume) :=
    isFiniteMeasure_of_le σ (Measure.singularPart_le σ volume)
  have hνf := isFiniteMeasure_blowMeasure x₀ r hc (σ.singularPart volume)
  obtain ⟨W, hWo, hWU, hWvol, ε₀, hε₀, hε⟩ := concentration
    (blowMeasure x₀ r (blowConst σ x₀ r) (σ.singularPart volume))
    (blowMeasure_singularPart_mutuallySingular x₀ r _ σ hr.ne') (isOpen_euclideanBall _ _) hη
  refine ⟨W, hWo, hWU, hWvol, ε₀, hε₀, fun ε hεI => ?_⟩
  have hB := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1
    (blowMeasure_euclideanBall_half_ge x₀ r σ hd hr hpos (measure_lt_top _ _) hG4)
  exact hB.trans (hε ε hεI)

theorem integrable_piEuclideanNorm_of_integrable {τ : Measure (Vec d)} {f : Vec d → ι → ℝ}
    (hf : Integrable f τ) : Integrable (fun y => piEuclideanNorm (f y)) τ :=
  integrable_piEuclideanNorm_of_coord fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hf

theorem contDiff_mollMuK {σ : Measure (Vec d)} [IsFiniteMeasure σ] {x₀ : Vec d} {r : ℝ} (hr : 0 < r)
    {c : ℝ≥0∞} (hc : c ≠ ∞) {P : Vec d → ι → ℝ} (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (mollMuK x₀ r c ε σ P) :=
  contDiff_mollify hε _ (integrable_blowDensity x₀ hr.ne' hc hP)

theorem contDiff_mollVK {σ : Measure (Vec d)} [IsFiniteMeasure σ] {x₀ : Vec d} {r : ℝ} (hr : 0 < r)
    {c : ℝ≥0∞} (hc : c ≠ ∞) {P : Vec d → ι → ℝ} (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε)
    (P0 : ι → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (mollVK x₀ r c ε σ P P0) :=
  (contDiff_mollMuK hr hc hP hε).sub ((contDiff_mollU hc hε).smul contDiff_const)

theorem mollVK_eq {σ : Measure (Vec d)} [IsFiniteMeasure σ] {x₀ : Vec d} {r : ℝ} (hr : 0 < r)
    {c : ℝ≥0∞} (hc : c ≠ ∞) {P : Vec d → ι → ℝ} (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε)
    (P0 : ι → ℝ) (x : Vec d) :
    mollVK x₀ r c ε σ P P0 x =
      mollify ε (blowMeasure x₀ r c (volume.withDensity (σ.rnDeriv volume))) (blowDensity x₀ r P) x +
      mollify ε (blowMeasure x₀ r c (σ.singularPart volume))
        (fun y => blowDensity x₀ r P y - P0) x := by
  have hint := integrable_blowDensity x₀ hr.ne' hc hP (c := c)
  have hα : blowMeasure x₀ r c (volume.withDensity (σ.rnDeriv volume)) ≤ blowMeasure x₀ r c σ :=
    blowMeasure_mono x₀ r c (Measure.withDensity_rnDeriv_le σ volume)
  have hν : blowMeasure x₀ r c (σ.singularPart volume) ≤ blowMeasure x₀ r c σ :=
    blowMeasure_mono x₀ r c (Measure.singularPart_le σ volume)
  have hΦ := (contDiff_scaledMollifier (d := d) ε).continuous
  have hc' := hasCompactSupport_scaledMollifier (d := d) hε
  have k1 := integrable_kernel hΦ hc' (hint.mono_measure hα) x
  have k2 := integrable_kernel hΦ hc' (hint.mono_measure hν) x
  have k3 : Integrable (fun y => scaledMollifier ε (x - y) • P0)
      (blowMeasure x₀ r c (σ.singularPart volume)) := by
    have := integrable_kernel hΦ hc' (E := ι → ℝ)
      (τ := blowMeasure x₀ r c (σ.singularPart volume)) (f := fun _ => P0) (by
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
  have hu : mollU x₀ r c ε σ x • P0 =
      ∫ y, scaledMollifier ε (x - y) • P0 ∂blowMeasure x₀ r c (σ.singularPart volume) := by
    unfold mollU mollifyMeasure mollify
    rw [← integral_smul_const]
    simp
  unfold mollVK mollMuK
  rw [hsplit, hu]
  unfold mollify
  simp only [smul_sub]
  rw [integral_sub k2 k3]
  abel

theorem integral_mollVK_le {σ : Measure (Vec d)} [IsFiniteMeasure σ] {x₀ : Vec d} {r : ℝ}
    (hr : 0 < r) (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r))
    {P : Vec d → ι → ℝ} (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∫ x in euclideanBall (0 : Vec d) (7 / 8),
        piEuclideanNorm (mollVK x₀ r (blowConst σ x₀ r) ε σ P (P x₀) x) ≤
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
  have hna : IntegrableOn (fun x => piEuclideanNorm (mollify ε α (blowDensity x₀ r P) x)) B :=
    integrableOn_euclideanBall_of_continuous (continuous_piEuclideanNorm.comp ha.continuous)
      (by norm_num) (by norm_num)
  have hnb : IntegrableOn
      (fun x => piEuclideanNorm (mollify ε ν (fun y => blowDensity x₀ r P y - P x₀) x)) B :=
    integrableOn_euclideanBall_of_continuous (continuous_piEuclideanNorm.comp hb.continuous)
      (by norm_num) (by norm_num)
  have hstep : ∀ x, piEuclideanNorm (mollVK x₀ r c ε σ P (P x₀) x) ≤
      piEuclideanNorm (mollify ε α (blowDensity x₀ r P) x) +
      piEuclideanNorm (mollify ε ν (fun y => blowDensity x₀ r P y - P x₀) x) := by
    intro x
    rw [mollVK_eq hr hc hP hε]
    exact piEuclideanNorm_add_le _ _
  have hV : IntegrableOn (fun x => piEuclideanNorm (mollVK x₀ r c ε σ P (P x₀) x)) B :=
    integrableOn_euclideanBall_of_continuous (continuous_piEuclideanNorm.comp
      (contDiff_mollVK hr hc hP hε _).continuous) (by norm_num) (by norm_num)
  have h1 := integral_piEuclideanNorm_mollify_le hε α hintα hB
  have h2 := integral_piEuclideanNorm_mollify_le hε ν hintν' hB
  have hsub : {y : Vec d | ∃ x ∈ B, x ∈ euclideanBall y ε} ⊆ Metric.closedBall 0 1 :=
    Set.Subset.trans (thickening_subset hε hε8) euclideanBall_one_subset_closedBall_one
  have m1 : ∫ y in {y : Vec d | ∃ x ∈ B, x ∈ euclideanBall y ε},
        piEuclideanNorm (blowDensity x₀ r P y) ∂α ≤
      ∫ y in Metric.closedBall 0 1, piEuclideanNorm (blowDensity x₀ r P y) ∂α :=
    setIntegral_mono_set (integrable_piEuclideanNorm_of_integrable hintα).integrableOn
      (Eventually.of_forall fun _ => piEuclideanNorm_nonneg _) hsub.eventuallyLE
  have m2 : ∫ y in {y : Vec d | ∃ x ∈ B, x ∈ euclideanBall y ε},
        piEuclideanNorm (blowDensity x₀ r P y - P x₀) ∂ν ≤
      ∫ y in Metric.closedBall 0 1, piEuclideanNorm (blowDensity x₀ r P y - P x₀) ∂ν :=
    setIntegral_mono_set (integrable_piEuclideanNorm_of_integrable hintν').integrableOn
      (Eventually.of_forall fun _ => piEuclideanNorm_nonneg _) hsub.eventuallyLE
  calc _ ≤ ∫ x in B, (piEuclideanNorm (mollify ε α (blowDensity x₀ r P) x) +
        piEuclideanNorm (mollify ε ν (fun y => blowDensity x₀ r P y - P x₀) x)) :=
        setIntegral_mono hV (hna.add hnb) hstep
    _ = _ := integral_add hna hnb
    _ ≤ _ := by
        unfold blowDelta
        exact add_le_add (h1.trans m1) (h2.trans m2)

theorem integral_mollMuK_le {σ : Measure (Vec d)} [IsFiniteMeasure σ] {x₀ : Vec d} {r : ℝ}
    (hr : 0 < r) (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r))
    {P : Vec d → ι → ℝ} (hP : Integrable P σ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∫ x in euclideanBall (0 : Vec d) (7 / 8),
        piEuclideanNorm (mollMuK x₀ r (blowConst σ x₀ r) ε σ P x) ≤
      piEuclideanNorm (P x₀) + blowDelta σ x₀ P r := by
  have hc := blowConst_ne_top hpos
  set c := blowConst σ x₀ r with hcdef
  have hu := integral_mollU_le_one hr hpos (measure_lt_top _ _) hε hε8 (σ := σ)
  have hv := integral_mollVK_le hr hpos hP hε hε8
  have hstep : ∀ x, piEuclideanNorm (mollMuK x₀ r c ε σ P x) ≤
      piEuclideanNorm (mollVK x₀ r c ε σ P (P x₀) x) +
        piEuclideanNorm (P x₀) * mollU x₀ r c ε σ x := by
    intro x
    rw [mollMuK_eq x₀ r c ε σ P (P x₀) x, add_comm]
    refine (piEuclideanNorm_add_le _ _).trans ?_
    rw [piEuclideanNorm_smul, abs_of_nonneg (mollU_nonneg hε.le σ x), mul_comm]
  have hVi : IntegrableOn (fun x => piEuclideanNorm (mollVK x₀ r c ε σ P (P x₀) x))
      (euclideanBall (0 : Vec d) (7 / 8)) :=
    integrableOn_euclideanBall_of_continuous (continuous_piEuclideanNorm.comp
      (contDiff_mollVK hr hc hP hε _).continuous) (by norm_num) (by norm_num)
  have hUi : IntegrableOn (fun x => piEuclideanNorm (P x₀) * mollU x₀ r c ε σ x)
      (euclideanBall (0 : Vec d) (7 / 8)) :=
    (integrableOn_euclideanBall_of_continuous (contDiff_mollU hc hε (σ := σ)
      (x₀ := x₀) (r := r)).continuous (by norm_num) (by norm_num)).const_mul _
  have hMi : IntegrableOn (fun x => piEuclideanNorm (mollMuK x₀ r c ε σ P x))
      (euclideanBall (0 : Vec d) (7 / 8)) :=
    integrableOn_euclideanBall_of_continuous (continuous_piEuclideanNorm.comp
      (contDiff_mollMuK hr hc hP hε).continuous) (by norm_num) (by norm_num)
  calc _ ≤ ∫ x in euclideanBall (0 : Vec d) (7 / 8), (piEuclideanNorm (mollVK x₀ r c ε σ P (P x₀) x) +
        piEuclideanNorm (P x₀) * mollU x₀ r c ε σ x) := setIntegral_mono hMi (hVi.add hUi) hstep
    _ = _ := integral_add hVi hUi
    _ ≤ _ := by
        rw [integral_const_mul]
        have := mul_le_mul_of_nonneg_left hu (piEuclideanNorm_nonneg (P x₀))
        linarith

/-- For `0 < r ≤ r̄` with `σˢ(Q_r(x₀)) > 0` and `ε ∈ (0, 1/8]`: `∫_{B_{7/8}} u ≤ 1`,
`∫_{B_{7/8}} |V| ≤ δ(r)`, `∫_{B_{7/8}} |μ| ≤ |P₀| + δ(r)` (`P₀ = P(x₀)`), and
`∫_{B_{7/8}} |Y_{α,β}| ≤ C_A r (|P₀| + δ(r))`. Since `δ(r) → 0` (smallness of the mollified blow-ups) and `r_j → 0`, all errors tend
to `0`. -/
theorem lem_smallk {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {k : ℕ}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω) {x₀ : Vec d} {P0 : ι → ℝ}
    {c0 rb CA : ℝ} (hs : IsBlowSettingK Ω k A x₀ P0 c0 rb CA) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ rb)
    {σ : Measure (Vec d)} [IsFiniteMeasure σ] {P : Vec d → ι → ℝ} (hPm : Measurable P)
    (hPi : Integrable P σ) (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r)) {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    (∫ x in euclideanBall (0 : Vec d) (7 / 8), mollU x₀ r (blowConst σ x₀ r) ε σ x ≤ 1) ∧
    (∫ x in euclideanBall (0 : Vec d) (7 / 8),
        piEuclideanNorm (mollVK x₀ r (blowConst σ x₀ r) ε σ P (P x₀) x) ≤
      blowDelta σ x₀ P r) ∧
    (∫ x in euclideanBall (0 : Vec d) (7 / 8),
        piEuclideanNorm (mollMuK x₀ r (blowConst σ x₀ r) ε σ P x) ≤
      piEuclideanNorm (P x₀) + blowDelta σ x₀ P r) ∧
    ∀ α β : Fin d → ℕ, multiAbs α ≤ k → β ∈ multiLE α →
      ∫ x in euclideanBall (0 : Vec d) (7 / 8),
          piEuclideanNorm (errY x₀ r (blowConst σ x₀ r) ε σ A P α β x) ≤
        CA * r * (piEuclideanNorm (P x₀) + blowDelta σ x₀ P r) :=
  ⟨integral_mollU_le_one hr0 hpos (measure_lt_top _ _) hε hε8,
    integral_mollVK_le hr0 hpos hPi hε hε8, integral_mollMuK_le hr0 hpos hPi hε hε8,
    fun _ _ hα hβ => integral_errY_le hΩ hA hs hr0 hr1 hPm hPi hpos hε hε8 hα hβ⟩

end

end AFree
