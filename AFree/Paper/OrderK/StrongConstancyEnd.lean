module

public import AFree.Analysis.Fava
public import AFree.Analysis.Bump
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# The endgame of strong constancy

The last steps of strong constancy (negative parts uniformly integrable, Vitali lemma on
`closed B_{3/4}`, definition of `w`), for the real sequences `w_j` and `h_j` of order `k`.
-/

@[expose] public section

open MeasureTheory PDE Filter Topology

namespace AFree

noncomputable section

variable {d : ℕ}

theorem unifIntegrable_one_of_abs_le {μ : Measure (Vec d)} {f g : ℕ → Vec d → ℝ}
    (hf : UnifIntegrable f 1 μ) (hgm : ∀ i, AEStronglyMeasurable (g i) μ)
    (hg : ∀ i x, ‖g i x‖ ≤ ‖f i x‖) : UnifIntegrable g 1 μ := by
  rw [unifIntegrable_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf ε hε
  exact ⟨δ, hδ, fun i s hs =>
    (eLpNorm_mono (hgm i).restrict (fun x => hg i x)).trans (h i s hs)⟩

/-- The endgame: `w_i ≥ 0` supported in `closed B_{3/4}`, `h_i → h` in `L¹(B₁)`, `w_i - h_i`
distributionally and in measure small from below; then `w_i → h 1_{closed B_{3/4}}` in `L¹`. -/
theorem sc_endgame {ws hR : ℕ → Vec d → ℝ} {hL : Vec d → ℝ}
    (hwi : ∀ i, Integrable (ws i)) (hw0 : ∀ i x, 0 ≤ ws i x)
    (hwsupp : ∀ i, tsupport (ws i) ⊆ euclideanClosedBall (0 : Vec d) (3 / 4))
    (hhi : ∀ i, IntegrableOn (hR i) (euclideanBall (0 : Vec d) 1))
    (hg : IntegrableOn hL (euclideanBall (0 : Vec d) 1))
    (hgt : Tendsto (fun i => ∫ x in euclideanBall (0 : Vec d) 1, |hR i x - hL x|) atTop (𝓝 0))
    (ha : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanBall (0 : Vec d) 1 →
      Tendsto (fun i => ∫ x, ψ x * (ws i x - hR i x)) atTop (𝓝 0))
    (hb : ∀ l : ℝ, 0 < l → Tendsto (fun i => volume {x ∈ euclideanBall (0 : Vec d) 1 |
      l < max (-(ws i x - hR i x)) 0}) atTop (𝓝 0)) :
    ∃ W : Vec d → ℝ, Integrable W ∧
      Tendsto (fun i => ∫ x, |ws i x - W x|) atTop (𝓝 0) := by
  set B1 := euclideanBall (0 : Vec d) 1 with hB1
  set fi : ℕ → Vec d → ℝ := fun i x => ws i x - hR i x with hfi
  have hint : ∀ i, IntegrableOn (fi i) B1 := fun i => (hwi i).integrableOn.sub (hhi i)
  have hL1 : Tendsto (fun i => eLpNorm (hR i - hL) 1 (volume.restrict B1)) atTop (𝓝 0) := by
    have h1 : ∀ i, eLpNorm (hR i - hL) 1 (volume.restrict B1) =
        ENNReal.ofReal (∫ x in B1, |hR i x - hL x|) := fun i => by
      rw [eLpNorm_one_eq_lintegral_enorm ((hhi i).sub hg).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm ((hhi i).sub hg)]
      simp only [Pi.sub_apply, Real.norm_eq_abs]
    simp only [h1]
    simpa using ENNReal.tendsto_ofReal hgt
  have hunif := unifIntegrable_of_tendsto_Lp (μ := volume.restrict B1) (f := hR) le_rfl
    ENNReal.one_ne_top (fun i => memLp_one_iff_integrable.2 (hhi i))
    (memLp_one_iff_integrable.2 hg) hL1
  have hc : UnifIntegrable (fun i => fun x => max (-fi i x) 0) 1 (volume.restrict B1) :=
    unifIntegrable_one_of_abs_le hunif (fun i => ((hint i).neg.pos_part).aestronglyMeasurable)
      (fun i x => by
        have h1 := hw0 i x
        simp only [hfi, Real.norm_eq_abs]
        rw [abs_of_nonneg (le_max_right _ _)]
        refine max_le ?_ (abs_nonneg _)
        have := le_abs_self (hR i x)
        linarith)
  set K := euclideanClosedBall (0 : Vec d) (3 / 4) with hK
  have hKc : IsCompact K := isCompact_euclideanClosedBall _ (by norm_num)
  have hKB : K ⊆ B1 := euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num)
  have hV := tendsto_setIntegral_abs_of_vitali fi hint ha hb hc hKc hKB
  have hKm : MeasurableSet K := hKc.measurableSet
  refine ⟨K.indicator hL, (hg.mono_set hKB).integrable_indicator hKm, ?_⟩
  refine squeeze_zero (fun i => integral_nonneg fun x => abs_nonneg _) (fun i => ?_)
    (by simpa using hV.add hgt)
  have hgK : IntegrableOn hL K := hg.mono_set hKB
  have hsupp : ∀ x ∉ K, |ws i x - K.indicator hL x| = 0 := by
    intro x hx
    have : ws i x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hwsupp _ h)
    simp [this, Set.indicator_of_notMem hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) hsupp]
  have hfK : IntegrableOn (fun x => |fi i x|) K := ((hint i).mono_set hKB).abs
  have hhK : IntegrableOn (fun x => |hR i x - hL x|) B1 := ((hhi i).sub hg).abs
  calc ∫ x in K, |ws i x - K.indicator hL x|
      ≤ ∫ x in K, (|fi i x| + |hR i x - hL x|) := by
        refine setIntegral_mono_on ?_ (hfK.add (hhK.mono_set hKB)) hKm fun x hx => ?_
        · have h0 : IntegrableOn (fun x => |ws i x - hL x|) K :=
            (((hwi i).integrableOn).sub hgK).abs
          exact h0.congr_fun (fun x hx => by simp [Set.indicator_of_mem hx]) hKm
        · rw [Set.indicator_of_mem hx]
          have : ws i x - hL x = fi i x + (hR i x - hL x) := by simp only [hfi]; ring
          rw [this]
          exact abs_add_le _ _
    _ = (∫ x in K, |fi i x|) + ∫ x in K, |hR i x - hL x| :=
        integral_add hfK (hhK.mono_set hKB)
    _ ≤ _ := add_le_add le_rfl (setIntegral_mono_set hhK
          (Filter.Eventually.of_forall fun x => abs_nonneg _) (Filter.Eventually.of_forall hKB))

end

end AFree
