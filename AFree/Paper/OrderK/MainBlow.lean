module

public import AFree.Paper.OrderK.Blow
public import AFree.Paper.OrderK.SC
public import AFree.Paper.OrderK.MainBlowData
public import AFree.Measure.Concentration
public import AFree.Analysis.Bump

/-!
# The blow-up contradiction for `d, k ≥ 1`

If the bad set `E` has positive singular measure, the blow-up at a good point, the cut-off system and
strong constancy of order `k` contradict the concentration of `σˢ`; see [DPR, Section 2.3].
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix PDE
open scoped ENNReal

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- For `d, k ≥ 1`, `σˢ(E) = 0`, where `E` is the bad set
`{x ∈ Ω : P x ∉ Λ_x}` of order `k`. -/
theorem thm_main_pair_blowup (hd : 0 < d) {k : ℕ} (hk : 1 ≤ k) {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω)
    (σ : Measure (Vec d)) [IsFiniteMeasure σ] {P : Vec d → ι → ℝ} (hPm : Measurable P)
    (hPi : Integrable P σ) (h : IsFreePairVar Ω k A σ P) :
    σ.singularPart volume (badSetK Ω k A P) = 0 := by
  by_contra hne
  have hpos : 0 < σ.singularPart volume (badSetK Ω k A P) := pos_iff_ne_zero.2 hne
  obtain ⟨x₀, hxE, hxΩ, hposB, hG2, hG3, hG4⟩ := lem_goodk hd k σ hPm hPi h.1 hpos
  set t : ℝ := badT d with ht
  have ht0 : 0 < t := badT_pos hd
  set P₀ : ι → ℝ := P x₀ with hP₀
  obtain ⟨c0, rb, CA, hs⟩ := exists_blowSettingK hd hΩ k hA hxΩ hxE.2
  have hrb0 : 0 < rb := hs.hrb0
  have hrb1 : rb ≤ 1 := hs.hrb1
  -- the radii
  have hrad : ∀ j : ℕ, ∃ r ∈ Ioo (0 : ℝ) (rb / (j + 1)),
      ENNReal.ofReal (t ^ (d + 1)) * σ.singularPart volume (Metric.closedBall x₀ r) ≤
        σ.singularPart volume (Metric.closedBall x₀ (t * r)) := fun j =>
    hG4 _ (by positivity)
  choose r hr hr4 using hrad
  have hr0 : ∀ j, 0 < r j := fun j => (hr j).1
  have hrle : ∀ j, r j ≤ rb := fun j => by
    have := (hr j).2
    have h1 : rb / (j + 1) ≤ rb :=
      div_le_self hrb0.le (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
    linarith
  have hr1 : ∀ j, r j ≤ 1 := fun j => (hrle j).trans hrb1
  have hrt0 : Tendsto r atTop (𝓝 0) := by
    have : Tendsto (fun j : ℕ => rb / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat rb |>.comp (tendsto_add_atTop_nat 1) |>.congr
        fun j => by simp
    exact squeeze_zero (fun j => (hr0 j).le) (fun j => (hr j).2.le) this
  have hrt : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hrt0, Eventually.of_forall hr0⟩
  have hposj : ∀ j, 0 < σ.singularPart volume (Metric.closedBall x₀ (r j)) := fun j =>
    hposB _ (hr0 j)
  -- the concentration
  have hη : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have hconc := fun j : ℕ => exists_epsK hd σ x₀ (hr0 j) (hposj j) (hr4 j) (hη j)
  choose W hWo hWU hWvol ε₀ hε₀ hconc using hconc
  set ε : ℕ → ℝ := fun j => min (ε₀ j) (1 / 8) with hε
  have hε0 : ∀ j, 0 < ε j := fun j => lt_min (hε₀ j) (by norm_num)
  have hε8 : ∀ j, ε j ≤ 1 / 8 := fun j => min_le_right _ _
  have hεm : ∀ j, ε j ∈ Ioc 0 (ε₀ j) := fun j => ⟨hε0 j, min_le_left _ _⟩
  -- the blow-up data
  have hdata := fun j => blowStepK hΩ hA hPm hPi h rfl hs (hr0 j) (hrle j) (hposj j) (hε0 j)
    (hε8 j)
  set u : ℕ → Vec d → ℝ := fun j => mollU x₀ (r j) (blowConst σ x₀ (r j)) (ε j) σ with hu
  set V : ℕ → Vec d → ι → ℝ := fun j => mollVK x₀ (r j) (blowConst σ x₀ (r j)) (ε j) σ P P₀
    with hV
  set μ : ℕ → Vec d → ι → ℝ := fun j => mollMuK x₀ (r j) (blowConst σ x₀ (r j)) (ε j) σ P
    with hμ
  set Y : ℕ → (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ := fun j =>
    errYk k x₀ (r j) (blowConst σ x₀ (r j)) (ε j) σ A P with hY
  set δ : ℕ → ℝ := fun j => blowDelta σ x₀ P (r j) with hδ
  have hδt : Tendsto δ atTop (𝓝 0) := (tendsto_blowDelta σ x₀ P hG2 hG3).comp hrt
  -- the cut-off system
  set χ : Vec d → ℝ := euclideanCutoff (1 / 2) (3 / 4) with hχ
  obtain ⟨H, hw, hw0, hws, hG, hH, hGs, hsys, hGsmall, hHb, hwb⟩ :=
    lem_systemk (fun α => A α x₀) P₀ (contDiff_euclideanCutoff _ _)
      (hasCompactSupport_euclideanCutoff (by norm_num) (by norm_num))
      (euclideanCutoff_nonneg _ _) (euclideanCutoff_le_one _ _) tsupport_euclideanCutoff_half CA
      hs.hCA (fun j => (hr0 j).le) hr1 hrt0 (fun j => blowDelta_nonneg σ x₀ P (r j)) hδt
      (u := u) (V := V) (μ := μ) (Y := Y)
      (fun j => (hdata j).1) (fun j => (hdata j).2.1) (fun j => (hdata j).2.2.1)
      (fun j => (hdata j).2.2.2.1) (fun j => (hdata j).2.2.2.2.1)
      (fun j => (hdata j).2.2.2.2.2.1) (fun j => (hdata j).2.2.2.2.2.2.1)
      (fun j => (hdata j).2.2.2.2.2.2.2.1) (fun j => (hdata j).2.2.2.2.2.2.2.2.1)
      (fun j => (hdata j).2.2.2.2.2.2.2.2.2.1) (fun j => (hdata j).2.2.2.2.2.2.2.2.2.2)
  obtain ⟨φ, hφ, wInf, hwI, hlim⟩ := prop_sck hd hk (fun α => A α x₀) P₀ hs.hc0 hs.hell
    (fun j x => χ x * u j x) _ H hw hG hH hw0 hws hGs hsys hGsmall hHb hwb
  -- the contradiction
  have hVol : Tendsto (fun i => volume (W (φ i))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h1.comp hφ.tendsto_atTop) (fun _ => bot_le) (fun i => (hWvol (φ i)).le)
  have hAbs := (hwI.abs).tendsto_setIntegral_nhds_zero (l := atTop) (s := fun i => W (φ i)) hVol
  have hup : Tendsto (fun i : ℕ => 1 / (((φ i : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hsum : Tendsto (fun i => (∫ x, |χ x * u (φ i) x - wInf x|) +
      (∫ x in W (φ i), |wInf x|) + 1 / (((φ i : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    simpa using (hlim.add hAbs).add hup
  have hfin : t ^ (d + 1) ≤ 0 := by
    refine ge_of_tendsto' hsum fun i => ?_
    set j := φ i
    refine (hconc j (ε j) (hεm j)).trans ?_
    have hwint : Integrable (fun x => χ x * u j x) := (hw j).1.continuous.integrable_of_hasCompactSupport
      (hw j).2
    have hdiff : Integrable (fun x => |χ x * u j x - wInf x|) := (hwint.sub hwI).abs
    have hu1 : ∫ x in W j, u j x = ∫ x in W j, χ x * u j x := by
      refine setIntegral_congr_fun (hWo j).measurableSet fun x hx => ?_
      simp only [hχ, euclideanCutoff_half_eq_one (hWU j hx), one_mul]
    have h1 : ∫ x in W j, χ x * u j x ≤
        ∫ x in W j, (|χ x * u j x - wInf x| + |wInf x|) := by
      refine setIntegral_mono hwint.integrableOn (hdiff.add hwI.abs).integrableOn fun x => ?_
      have := abs_sub_abs_le_abs_sub (χ x * u j x) (wInf x)
      have := le_abs_self (χ x * u j x)
      linarith [abs_nonneg (wInf x)]
    rw [integral_add hdiff.integrableOn hwI.abs.integrableOn] at h1
    have h2 : ∫ x in W j, |χ x * u j x - wInf x| ≤ ∫ x, |χ x * u j x - wInf x| :=
      setIntegral_le_integral hdiff (Eventually.of_forall fun _ => abs_nonneg _)
    show (∫ x in W j, u j x) + 1 / ((j : ℝ) + 1) ≤ _
    rw [hu1]
    linarith
  exact absurd hfin (not_le.2 (by positivity))

end

end AFree
