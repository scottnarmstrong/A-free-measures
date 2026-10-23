module

public import AFree.Paper.OrderK.BlowUpErr
public import AFree.Paper.Elliptic.Mollified

/-!
# The `L¹` size of the mollified coefficient errors

The `L¹` bound `∫_{B_{7/8}} |Y_{α,β}| ≤ C_A r (|P₀| + δ)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix PDE
open scoped ENNReal

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem measurable_euclideanCoordDeriv (g : Vec d → ℝ) (i : Fin d) :
    Measurable (euclideanCoordDeriv i g) := by
  unfold euclideanCoordDeriv
  exact (measurable_fderiv ℝ g).apply_continuousLinearMap (basisVec i)

theorem measurable_multiCoordDeriv_of_ne (g : Vec d → ℝ) {γ : Fin d → ℕ} (hγ : γ ≠ 0) :
    Measurable (multiCoordDeriv γ g) := by
  have key : ∀ l : List (Fin d), (∃ i ∈ l, γ i ≠ 0) → Measurable (foldDeriv l γ g) := by
    intro l
    induction l with
    | nil => rintro ⟨i, hi, _⟩; exact absurd hi (by simp)
    | cons j l ih =>
      intro h
      show Measurable ((euclideanCoordDeriv j)^[γ j] (foldDeriv l γ g))
      by_cases hj : γ j = 0
      · rw [hj]
        obtain ⟨i, hi, hγi⟩ := h
        rcases List.mem_cons.1 hi with rfl | hi'
        · exact absurd hj hγi
        · exact ih ⟨i, hi', hγi⟩
      · obtain ⟨n, hn⟩ : ∃ n, γ j = n + 1 := ⟨γ j - 1, by omega⟩
        rw [hn, Function.iterate_succ_apply']
        exact measurable_euclideanCoordDeriv _ j
  refine key (List.finRange d) ?_
  by_contra hne
  push Not at hne
  exact hγ (funext fun i => hne i (List.mem_finRange i))

theorem piEuclideanNorm_add_le (a b : ι → ℝ) :
    piEuclideanNorm (a + b) ≤ piEuclideanNorm a + piEuclideanNorm b := by
  have h := sum_mul_le_piEuclideanNorm_mul a b
  have ha := sum_mul_self_eq_sq a
  have hb := sum_mul_self_eq_sq b
  have hab : ∑ i, (a + b) i * (a + b) i = piEuclideanNorm a ^ 2 + 2 * ∑ i, a i * b i +
      piEuclideanNorm b ^ 2 := by
    rw [← ha, ← hb, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  unfold piEuclideanNorm at *
  rw [Real.sqrt_le_left (by positivity), hab]
  nlinarith [Real.sqrt_nonneg (∑ i, a i * a i), Real.sqrt_nonneg (∑ i, b i * b i)]

theorem piEuclideanNorm_sub_le (a b : ι → ℝ) :
    piEuclideanNorm a ≤ piEuclideanNorm (a - b) + piEuclideanNorm b := by
  have := piEuclideanNorm_add_le (a - b) b
  simpa using this

theorem integral_closedBall_one_blowDensity_le {σ : Measure (Vec d)} [IsFiniteMeasure σ]
    {P : Vec d → ι → ℝ} (hP : Integrable P σ) (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r)) :
    ∫ z in Metric.closedBall (0 : Vec d) 1,
        piEuclideanNorm (blowDensity x₀ r P z) ∂blowMeasure x₀ r (blowConst σ x₀ r) σ ≤
      piEuclideanNorm (P x₀) + blowDelta σ x₀ P r := by
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
  have hcoordα : ∀ i, Integrable (fun z => blowDensity x₀ r P z i) α := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hintα
  have hcoordν : ∀ i, Integrable (fun z => blowDensity x₀ r P z i) ν := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hintν
  have hnα := integrable_piEuclideanNorm_of_coord hcoordα
  have hnν := integrable_piEuclideanNorm_of_coord hcoordν
  have hν' : Integrable (fun z => blowDensity x₀ r P z - P x₀) ν := hintν.sub (integrable_const _)
  have hnν' := integrable_piEuclideanNorm_of_coord (σ := ν)
    (P := fun z => blowDensity x₀ r P z - P x₀) fun i =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hν'
  have hsplit : blowMeasure x₀ r c σ = α + ν := blowMeasure_eq_add x₀ r c σ
  have hν1 : ν (Metric.closedBall 0 1) = 1 :=
    blowMeasure_closedBall_one x₀ r σ hr hpos (measure_lt_top _ _)
  rw [hsplit, Measure.restrict_add, integral_add_measure hnα.restrict hnν.restrict]
  have h1 : ∫ z in Metric.closedBall (0 : Vec d) 1, piEuclideanNorm (blowDensity x₀ r P z) ∂ν ≤
      (∫ z in Metric.closedBall (0 : Vec d) 1,
        piEuclideanNorm (blowDensity x₀ r P z - P x₀) ∂ν) + piEuclideanNorm (P x₀) := by
    calc ∫ z in Metric.closedBall (0 : Vec d) 1, piEuclideanNorm (blowDensity x₀ r P z) ∂ν
        ≤ ∫ z in Metric.closedBall (0 : Vec d) 1,
          (piEuclideanNorm (blowDensity x₀ r P z - P x₀) + piEuclideanNorm (P x₀)) ∂ν := by
          refine integral_mono hnν.restrict (hnν'.restrict.add (integrable_const _)) fun z => ?_
          exact piEuclideanNorm_sub_le _ _
      _ = _ := by
          rw [integral_add hnν'.restrict (integrable_const _)]
          simp [Measure.real, hν1]
  unfold blowDelta
  linarith

theorem hmeasT (x₀ : Vec d) (r : ℝ) : Measurable fun z : Vec d => x₀ + r • z := by
  have h1 : Measurable fun z : Vec d => r • z := measurable_id.const_smul r
  exact (measurable_const : Measurable fun _ : Vec d => x₀).add h1

theorem aestronglyMeasurable_errDensity {Ω : Set (Vec d)} {k : ℕ}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω) {x₀ : Vec d} {P0 : ι → ℝ}
    {c0 rb CA : ℝ} (hs : IsBlowSettingK Ω k A x₀ P0 c0 rb CA) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ rb)
    {P : Vec d → ι → ℝ} (hPm : Measurable P) {α β : Fin d → ℕ} (hβ : β ∈ multiLE α)
    {τ : Measure (Vec d)} :
    AEStronglyMeasurable (errDensity x₀ r A P α β) τ := by
  have hBm : MeasurableSet (euclideanBall (0 : Vec d) 1) := measurableSet_euclideanBall _ _
  refine AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.2 fun j => ?_)
  have e : (fun z => errDensity x₀ r A P α β z j) = (euclideanBall (0 : Vec d) 1).indicator
      (fun z => ∑ i, errF x₀ r A α β z j i * blowDensity x₀ r P z i) := by
    funext z
    by_cases hz : z ∈ euclideanBall (0 : Vec d) 1
    · simp [errDensity, Set.indicator_of_mem hz, Matrix.mulVec, dotProduct]
    · simp [errDensity, Set.indicator_of_notMem hz]
  rw [e, aemeasurable_indicator_iff hBm]
  refine Finset.aemeasurable_fun_sum (M := ℝ) _ fun i _ => ?_
  have hP : AEMeasurable (fun z => blowDensity x₀ r P z i) (τ.restrict (euclideanBall (0 : Vec d) 1)) :=
    ((measurable_pi_apply i).comp (hPm.comp (hmeasT x₀ r))).aemeasurable
  refine AEMeasurable.mul ?_ hP
  · by_cases hαβ : β = α
    · subst hαβ
      have hc : ContinuousOn (fun z => errF x₀ r A β β z j i) (euclideanBall (0 : Vec d) 1) := by
        have : ContinuousOn (fun z : Vec d => A β (x₀ + r • z) j i - A β x₀ j i)
            (euclideanBall (0 : Vec d) 1) := by
          refine ContinuousOn.sub ?_ continuousOn_const
          refine ((hA β j i).continuousOn).comp (by fun_prop : Continuous fun z : Vec d => x₀ + r • z).continuousOn
            ?_
          intro z hz
          have hzQ : ‖z‖ ≤ 1 := by
            have := euclideanBall_one_subset_closedBall_one hz
            simpa using this
          refine hs.hQ ?_
          rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg hr0.le]
          nlinarith [norm_nonneg z, hs.hrb1]
        refine this.congr fun z _ => ?_
        simp [errF, multiCoordDeriv_zero, sub_self_pi]
      exact hc.aemeasurable hBm
    · have hγ0 : α - β ≠ 0 := by
        intro h0
        apply hαβ
        funext i
        have := congrFun h0 i
        have h2 := mem_multiLE.1 hβ i
        simp at this
        omega
      exact (measurable_multiCoordDeriv_of_ne _ hγ0).aemeasurable

theorem integrable_errDensity {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {k : ℕ}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω) {x₀ : Vec d} {P0 : ι → ℝ}
    {c0 rb CA : ℝ} (hs : IsBlowSettingK Ω k A x₀ P0 c0 rb CA) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ rb)
    {σ : Measure (Vec d)} {P : Vec d → ι → ℝ} (hPm : Measurable P) (hPi : Integrable P σ)
    {c : ℝ≥0∞} (hc : c ≠ ∞) {α β : Fin d → ℕ} (hα : multiAbs α ≤ k) (hβ : β ∈ multiLE α) :
    Integrable (errDensity x₀ r A P α β) (blowMeasure x₀ r c σ) := by
  have hPd := integrable_blowDensity x₀ hr0.ne' hc hPi (c := c)
  have hcoord : ∀ i, Integrable (fun z => blowDensity x₀ r P z i) (blowMeasure x₀ r c σ) := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hPd
  have hn := integrable_piEuclideanNorm_of_coord hcoord
  have hfb : ∀ z, piEuclideanNorm (errDensity x₀ r A P α β z) ≤
      CA * r * piEuclideanNorm (blowDensity x₀ r P z) := by
    intro z
    by_cases hz : z ∈ euclideanBall (0 : Vec d) 1
    · simp only [errDensity, Set.indicator_of_mem hz]
      exact errF_bound hΩ hA hs hr0 hr1 hα hβ hz _
    · simp only [errDensity, Set.indicator_of_notMem hz]
      have : piEuclideanNorm (0 : κ → ℝ) = 0 := by simp [piEuclideanNorm]
      rw [this]
      exact mul_nonneg (mul_nonneg hs.hCA hr0.le) (Real.sqrt_nonneg _)
  refine integrable_pi_iff.2 fun j => ?_
  refine Integrable.mono' (hn.const_mul (CA * r))
    ((continuous_apply j).comp_aestronglyMeasurable
      (aestronglyMeasurable_errDensity hA hs hr0 hr1 hPm hβ))
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_le_piEuclideanNorm _ j).trans (hfb z)

/-- `∫_{B_{7/8}} |Y_{α,β}| ≤ C_A r (|P₀| + δ)` for `ε ≤ 1/8`, `P₀ = P(x₀)`. -/
theorem integral_errY_le {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {k : ℕ}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω) {x₀ : Vec d} {P0 : ι → ℝ}
    {c0 rb CA : ℝ} (hs : IsBlowSettingK Ω k A x₀ P0 c0 rb CA) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ rb)
    {σ : Measure (Vec d)} [IsFiniteMeasure σ] {P : Vec d → ι → ℝ} (hPm : Measurable P)
    (hPi : Integrable P σ) (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r)) {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) {α β : Fin d → ℕ} (hα : multiAbs α ≤ k) (hβ : β ∈ multiLE α) :
    ∫ x in euclideanBall (0 : Vec d) (7 / 8),
        piEuclideanNorm (errY x₀ r (blowConst σ x₀ r) ε σ A P α β x) ≤
      CA * r * (piEuclideanNorm (P x₀) + blowDelta σ x₀ P r) := by
  have hc := blowConst_ne_top hpos
  set c := blowConst σ x₀ r with hcdef
  have hfin := isFiniteMeasure_blowMeasure x₀ r hc σ
  set τ := blowMeasure x₀ r c σ with hτ
  have hfi := integrable_errDensity hΩ hA hs hr0 hr1 hPm hPi hc hα hβ
  have hPd := integrable_blowDensity x₀ hr0.ne' hc hPi (c := c)
  have hcoord : ∀ i, Integrable (fun z => blowDensity x₀ r P z i) τ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hPd
  have hn := integrable_piEuclideanNorm_of_coord hcoord
  have hfb : ∀ z, piEuclideanNorm (errDensity x₀ r A P α β z) ≤
      CA * r * piEuclideanNorm (blowDensity x₀ r P z) := by
    intro z
    by_cases hz : z ∈ euclideanBall (0 : Vec d) 1
    · simp only [errDensity, Set.indicator_of_mem hz]
      exact errF_bound hΩ hA hs hr0 hr1 hα hβ hz _
    · simp only [errDensity, Set.indicator_of_notMem hz]
      have : piEuclideanNorm (0 : κ → ℝ) = 0 := by simp [piEuclideanNorm]
      rw [this]
      exact mul_nonneg (mul_nonneg hs.hCA hr0.le) (Real.sqrt_nonneg _)
  have hfcoord : ∀ j, Integrable (fun z => errDensity x₀ r A P α β z j) τ := fun j =>
    integrable_pi_iff.1 hfi j
  have hfn := integrable_piEuclideanNorm_of_coord hfcoord
  have h1 := integral_piEuclideanNorm_mollify_le hε τ hfi (measurableSet_euclideanBall (0 : Vec d) (7 / 8))
  have hsub : {y : Vec d | ∃ x ∈ euclideanBall (0 : Vec d) (7 / 8), x ∈ euclideanBall y ε} ⊆
      Metric.closedBall 0 1 :=
    (thickening_subset hε hε8).trans euclideanBall_one_subset_closedBall_one
  have hQm : MeasurableSet (Metric.closedBall (0 : Vec d) 1) := measurableSet_closedBall
  calc ∫ x in euclideanBall (0 : Vec d) (7 / 8),
        piEuclideanNorm (errY x₀ r c ε σ A P α β x)
      ≤ ∫ y in {y : Vec d | ∃ x ∈ euclideanBall (0 : Vec d) (7 / 8), x ∈ euclideanBall y ε},
          piEuclideanNorm (errDensity x₀ r A P α β y) ∂τ := h1
    _ ≤ ∫ y in Metric.closedBall (0 : Vec d) 1, piEuclideanNorm (errDensity x₀ r A P α β y) ∂τ :=
        setIntegral_mono_set hfn.integrableOn
          (Filter.Eventually.of_forall fun _ => piEuclideanNorm_nonneg _) hsub.eventuallyLE
    _ ≤ ∫ y in Metric.closedBall (0 : Vec d) 1, CA * r * piEuclideanNorm (blowDensity x₀ r P y) ∂τ :=
        setIntegral_mono_on hfn.integrableOn (hn.const_mul _).integrableOn hQm fun y _ => hfb y
    _ = CA * r * ∫ y in Metric.closedBall (0 : Vec d) 1, piEuclideanNorm (blowDensity x₀ r P y) ∂τ :=
        integral_const_mul _ _
    _ ≤ CA * r * (piEuclideanNorm (P x₀) + blowDelta σ x₀ P r) :=
        mul_le_mul_of_nonneg_left (integral_closedBall_one_blowDensity_le hPi x₀ hr0 hpos)
          (mul_nonneg hs.hCA hr0.le)

end

end AFree
