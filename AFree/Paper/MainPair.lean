module

public import AFree.Defs
public import AFree.Paper.FreePair
public import AFree.Paper.GoodPoints
public import AFree.Paper.BlowUp
public import AFree.Paper.Elliptic
public import AFree.Measure.Concentration
public import AFree.Measure.DimZero
public import AFree.Analysis.WaveCone
public import AFree.Analysis.StrongConstancy
public import AFree.Analysis.Bump

/-!
# The main theorem for 𝒜-free pairs

[DPR, Theorem 1.1] for first-order operators, for an 𝒜-free pair `(σ, P)` and `Fin` carriers.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal

namespace AFree

open PDE

/-- If `(σ, P)` is `𝒜`-free in `Ω`, then `P ∈ Λ_𝒜` at `σˢ`-a.e. point. -/
theorem ae_mem_waveCone_of_isFreePair {d m n : ℕ} {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {A : Fin d → Matrix (Fin n) (Fin m) ℝ} {A₀ : Matrix (Fin n) (Fin m) ℝ}
    (σ : Measure (Vec d)) [IsFiniteMeasure σ] {P : Vec d → Vec m}
    (hPm : Measurable P) (hPi : Integrable P σ) (h : IsFreePair Ω A A₀ σ P) :
    ∀ᵐ x ∂σ.singularPart volume, P x ∈ waveConeFirstOrder A := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ae_singularPart_dimZero σ _
  by_contra hne
  set E : Set (Vec d) := {x | P x ∉ waveConeFirstOrder A} with hE
  have hEm : MeasurableSet E :=
    ((isClosed_waveConeFirstOrder A).measurableSet.compl).preimage hPm
  have hpos : 0 < σ.singularPart volume E :=
    pos_iff_ne_zero.2 fun h0 => hne (ae_iff.2 h0)
  set t : ℝ := 1 / (4 * Real.sqrt d) with ht
  have hsd : 1 ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]; exact_mod_cast hd
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by
    rw [ht, div_lt_one (by positivity)]; linarith
  obtain ⟨x₀, hxE, hxΩ, hposB, hG2, hG3, hG4⟩ := exists_goodPoint σ hPm hPi h.1 ht0 ht1 hpos
  set P₀ : Vec m := P x₀ with hP₀
  obtain ⟨Λ, hΛ1, hMs, hM⟩ := exists_elliptic_ellipticMatrix A hxE
  -- the radius r̄
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩ x₀ hxΩ
  set rb : ℝ := min (ρ / 2) 1 with hrb
  have hrb0 : 0 < rb := lt_min (by positivity) one_pos
  have hrb1 : rb ≤ 1 := min_le_right _ _
  have hrbΩ : Metric.closedBall x₀ rb ⊆ Ω := fun y hy =>
    hρΩ (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy)
      (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ))))
  have hrad : ∀ j : ℕ, ∃ r ∈ Ioo (0 : ℝ) (rb / (j + 1)),
      ENNReal.ofReal (t ^ (d + 1)) * σ.singularPart volume (Metric.closedBall x₀ r) ≤
        σ.singularPart volume (Metric.closedBall x₀ (t * r)) := fun j =>
    hG4 _ (by positivity)
  choose r hr hr4 using hrad
  have hr0 : ∀ j, 0 < r j := fun j => (hr j).1
  have hr1 : ∀ j, r j ≤ 1 := fun j => by
    have := (hr j).2
    have h1 : rb / (j + 1) ≤ rb := div_le_self hrb0.le (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
    linarith
  have hrΩ : ∀ j, Metric.closedBall x₀ (r j) ⊆ Ω := fun j =>
    (Metric.closedBall_subset_closedBall (by
      have := (hr j).2
      have h1 : rb / (j + 1) ≤ rb :=
        div_le_self hrb0.le (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
      linarith)).trans hrbΩ
  have hrt : Tendsto r atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hr0⟩
    have : Tendsto (fun j : ℕ => rb / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat rb |>.comp (tendsto_add_atTop_nat 1) |>.congr
        fun j => by simp
    exact squeeze_zero (fun j => (hr0 j).le) (fun j => (hr j).2.le) this
  set c : ℕ → ℝ≥0∞ := fun j => blowConst σ x₀ (r j) with hc
  have hposj : ∀ j, 0 < σ.singularPart volume (Metric.closedBall x₀ (r j)) := fun j => hposB _ (hr0 j)
  have hfinj : ∀ j, σ.singularPart volume (Metric.closedBall x₀ (r j)) < ∞ := fun j =>
    measure_lt_top _ _
  have hcne : ∀ j, c j ≠ ∞ := fun j => blowConst_ne_top (hposj j)
  have hfinν : ∀ j, IsFiniteMeasure (blowMeasure x₀ (r j) (c j) (σ.singularPart volume)) :=
    fun j => by
      unfold blowMeasure
      exact Measure.smul_finite _ (hcne j)
  have hconc : ∀ j : ℕ, ∃ W : Set (Vec d), IsOpen W ∧ W ⊆ euclideanBall (0 : Vec d) (1 / 2) ∧
      volume W < ENNReal.ofReal (1 / ((j : ℝ) + 1)) ∧ ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
        (blowMeasure x₀ (r j) (c j) (σ.singularPart volume) (euclideanBall 0 (1 / 2))).toReal ≤
          (∫ x in W, mollifyMeasure ε (blowMeasure x₀ (r j) (c j) (σ.singularPart volume)) x) +
            1 / ((j : ℝ) + 1) := by
    intro j
    have := hfinν j
    exact concentration _ (blowMeasure_singularPart_mutuallySingular x₀ (r j) (c j) σ (hr0 j).ne')
      (isOpen_euclideanBall _ _) (by positivity)
  choose W hWo hWU hWvol ε₀ hε₀ hconc using hconc
  set ε : ℕ → ℝ := fun j => min (ε₀ j) (1 / 8) with hε
  have hε0 : ∀ j, 0 < ε j := fun j => lt_min (hε₀ j) (by norm_num)
  have hε8 : ∀ j, ε j ≤ 1 / 8 := fun j => min_le_right _ _
  have hεm : ∀ j, ε j ∈ Ioc 0 (ε₀ j) := fun j => ⟨hε0 j, min_le_left _ _⟩
  have hsys := fun j => leibniz_system h x₀ (hr0 j) (hrΩ j) (hcne j) hPi P₀ (hε0 j) (hε8 j)
  obtain ⟨K_G, K_H, hKG, hKH, hKb⟩ := leibniz_bounds A A₀ P₀ (d := d)
  have hδ : Tendsto (fun j => blowDelta σ x₀ P (r j)) atTop (𝓝 0) :=
    (tendsto_blowDelta σ x₀ P hG2 hG3).comp hrt
  have hbd := fun j => hKb σ P x₀ rfl hPi (hr0 j) (hr1 j) (hposj j) (hfinj j) (hε0 j) (hε8 j)
  have hGsmall : Tendsto (fun j => ∑ ℓ, ∫ x, vecEuclideanNorm
      (leibnizG A P₀ (mollV x₀ (r j) (c j) (ε j) σ P P₀) ℓ x)) atTop (𝓝 0) := by
    refine squeeze_zero (fun j => Finset.sum_nonneg fun ℓ _ =>
      integral_nonneg fun _ => vecEuclideanNorm_nonneg _) (fun j => (hbd j).1) ?_
    simpa using hδ.const_mul K_G
  obtain ⟨D, hD⟩ := hδ.bddAbove_range
  have hHbdd : ∃ C, ∀ j, ∫ x, vecEuclideanNorm
      (leibnizH A A₀ P₀ (r j) (mollMu x₀ (r j) (c j) (ε j) σ P) (mollU x₀ (r j) (c j) (ε j) σ)
        (mollV x₀ (r j) (c j) (ε j) σ P P₀) x) ≤ C :=
    ⟨K_H * (1 + vecEuclideanNorm P₀ + D), fun j =>
      (hbd j).2.trans (mul_le_mul_of_nonneg_left (by
        linarith [hD ⟨j, rfl⟩]) hKH)⟩
  obtain ⟨φ, hφ, wInf, hwI, hlim⟩ := exists_subseq_tendsto_L1_of_elliptic hd (by linarith : 0 < Λ)
    hMs hM (fun j => leibnizW (mollU x₀ (r j) (c j) (ε j) σ))
    (fun j ℓ => leibnizG A P₀ (mollV x₀ (r j) (c j) (ε j) σ P P₀) ℓ)
    (fun j => leibnizH A A₀ P₀ (r j) (mollMu x₀ (r j) (c j) (ε j) σ P)
      (mollU x₀ (r j) (c j) (ε j) σ) (mollV x₀ (r j) (c j) (ε j) σ P P₀))
    (fun j => (hsys j).2.1)
    (fun j => (isCompact_euclideanClosedBall (0 : Vec d) (by norm_num)).of_isClosed_subset
      (isClosed_tsupport _) (hsys j).2.2.1)
    (fun j => (hsys j).1) (fun j => (hsys j).2.2.1)
    (fun j ℓ => ((hsys j).2.2.2.1 ℓ).1) (fun j ℓ => ((hsys j).2.2.2.1 ℓ).2)
    (fun j => (hsys j).2.2.2.2.1) (fun j => (hsys j).2.2.2.2.2.1)
    (fun j x => (hsys j).2.2.2.2.2.2.2 x) hGsmall hHbdd
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
  have hsum : Tendsto (fun i => (∫ x, |leibnizW (mollU x₀ (r (φ i)) (c (φ i)) (ε (φ i)) σ) x -
      wInf x|) + (∫ x in W (φ i), |wInf x|) + 1 / (((φ i : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    simpa using (hlim.add hAbs).add hup
  have hfin : t ^ (d + 1) ≤ 0 := by
    refine ge_of_tendsto' hsum fun i => ?_
    set j := φ i
    have := hfinν j
    have hB := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1
      (blowMeasure_euclideanBall_half_ge x₀ (r j) σ hd (hr0 j) (hposj j) (hfinj j) (hr4 j))
    refine hB.trans ((hconc j (ε j) (hεm j)).trans ?_)
    have hu : ∫ x in W j, mollifyMeasure (ε j)
        (blowMeasure x₀ (r j) (c j) (σ.singularPart volume)) x =
        ∫ x in W j, leibnizW (mollU x₀ (r j) (c j) (ε j) σ) x := by
      refine setIntegral_congr_fun (hWo j).measurableSet fun x hx => ?_
      simp only [leibnizW, euclideanCutoff_half_eq_one (hWU j hx), one_mul]
      rfl
    rw [hu]
    have hwint : Integrable (leibnizW (mollU x₀ (r j) (c j) (ε j) σ)) :=
      ((hsys j).2.1.continuous).integrable_of_hasCompactSupport
        ((isCompact_euclideanClosedBall (0 : Vec d) (by norm_num)).of_isClosed_subset
          (isClosed_tsupport _) (hsys j).2.2.1)
    have hdiff : Integrable (fun x => |leibnizW (mollU x₀ (r j) (c j) (ε j) σ) x - wInf x|) :=
      (hwint.sub hwI).abs
    have h1 : ∫ x in W j, leibnizW (mollU x₀ (r j) (c j) (ε j) σ) x ≤
        ∫ x in W j, (|leibnizW (mollU x₀ (r j) (c j) (ε j) σ) x - wInf x| + |wInf x|) := by
      refine setIntegral_mono hwint.integrableOn (hdiff.add hwI.abs).integrableOn fun x => ?_
      have := abs_sub_abs_le_abs_sub (leibnizW (mollU x₀ (r j) (c j) (ε j) σ) x) (wInf x)
      have := le_abs_self (leibnizW (mollU x₀ (r j) (c j) (ε j) σ) x)
      linarith [abs_nonneg (wInf x)]
    rw [integral_add hdiff.integrableOn hwI.abs.integrableOn] at h1
    have h2 : ∫ x in W j, |leibnizW (mollU x₀ (r j) (c j) (ε j) σ) x - wInf x| ≤
        ∫ x, |leibnizW (mollU x₀ (r j) (c j) (ε j) σ) x - wInf x| :=
      setIntegral_le_integral hdiff (Eventually.of_forall fun _ => abs_nonneg _)
    linarith
  exact absurd hfin (not_le.2 (by positivity))

end AFree
