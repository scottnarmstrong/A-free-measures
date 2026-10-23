module

public import AFree.TopCurrents.Assembly.FlatChain

/-!
# [DPR, Theorem 1.15]: flat-chain identification, clauses (2) and (3) of `flat_main`
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace AFree

open PDE AFree.MetricCurrents.Nu

variable {d : ℕ}

/-- `|S(E)_top| ≤ |S|(E)`. -/
private lemma ofReal_abs_top_le {S : VectorMeasure (Vec d) (KVec d d)} (E : Set (Vec d)) :
    ENNReal.ofReal |S E (topKIdx d)| ≤ euclideanVariation S E :=
  (ENNReal.ofReal_le_ofReal (abs_apply_le_piEuclideanNorm (S E) _)).trans
    (ofReal_piEuclideanNorm_le_euclideanVariation S E)

/-- Clause (2)(i) of `flat_main`: the top coordinate of a flat chain is `u 𝓛^d`, `u ∈ L¹`. -/
theorem flat_chain_ac {S : VectorMeasure (Vec d) (KVec d d)} (hS : IsTopFlatChain S) :
    ∃ u : Vec d → ℝ, Integrable u volume ∧ coordMeasure S (topKIdx d) = volume.withDensityᵥ u := by
  set ν := coordMeasure S (topKIdx d) with hν
  have h2 : ν ≪ᵥ (volume : Measure (Vec d)).toENNRealVectorMeasure := by
    intro s hs
    by_cases hm : MeasurableSet s
    swap; · exact VectorMeasure.not_measurable _ hm
    rw [Measure.toENNRealVectorMeasure_apply_measurable hm] at hs
    by_contra hne
    have hpos : 0 < |ν s| := abs_pos.2 hne
    obtain ⟨N, hN, -, hlt⟩ := hS.2 (ENNReal.ofReal |ν s|) (ENNReal.ofReal_pos.2 hpos)
    have h0 := normalac hN hm hs
    have h1 : (S - N) s (topKIdx d) = ν s := by
      rw [sub_apply, Pi.sub_apply]
      have : N s (topKIdx d) = 0 := h0
      rw [this, sub_zero]; rfl
    have := (h1 ▸ ofReal_abs_top_le (S := S - N) s).trans (measure_mono (Set.subset_univ s))
    exact absurd (this.trans_lt hlt) (lt_irrefl _)
  exact ⟨_, SignedMeasure.integrable_rnDeriv _ _,
    (SignedMeasure.withDensityᵥ_rnDeriv_eq ν volume h2).symm⟩

/-- Clauses (2)(ii)-(iii) of `flat_main`: `T = u_#` is a compactly supported metric
current with `(∫ f dS)(top) = T(f, x)`. -/
theorem flat_chain_to_current {S : VectorMeasure (Vec d) (KVec d d)} (hS : IsTopFlatChain S) :
    ∃ T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ, IsMetricCurrent d T ∧ HasCompactAKSupport T ∧
      ∀ f, IsTestFunctionOn Set.univ f →
        (∫ᵛ x, f x ∂•S) (topKIdx d) = T f (fun i x => x i) := by
  obtain ⟨u, hui, hνu⟩ := flat_chain_ac hS
  obtain ⟨K, hKc, hKS⟩ := hS.1
  have happ : ∀ E, MeasurableSet E → S E (topKIdx d) = ∫ x in E, u x := fun E hE => by
    have := congrArg (fun m => m E) hνu
    simp only [coordMeasure_apply] at this
    rw [this, withDensityᵥ_apply hui hE]
  have hae : ∀ᵐ x, x ∉ K → u x = 0 := by
    have hKm := hKc.isClosed.measurableSet
    have := ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (μ := volume)
      (f := Kᶜ.indicator u)
      (fun s _ _ => (hui.indicator hKm.compl).integrableOn) fun s hs _ => by
        rw [setIntegral_indicator hKm.compl, ← happ _ (hs.inter hKm.compl)]
        have h1 := ofReal_abs_top_le (S := S) (s ∩ Kᶜ)
        have h2 : euclideanVariation S (s ∩ Kᶜ) = 0 :=
          le_antisymm ((measure_mono Set.inter_subset_right).trans hKS.le) bot_le
        rw [h2, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
        exact abs_nonpos_iff.1 h1
    filter_upwards [this] with x hx hxK
    simpa [hxK] using hx
  obtain ⟨hT, -, -, -, hsupp⟩ := usharp_isMetricCurrent hui
  refine ⟨usharp u, hT, hsupp K hKc hae, fun f hf => ?_⟩
  obtain ⟨hm, C, hC⟩ : Measurable f ∧ ∃ C, ∀ x, ‖f x‖ ≤ C :=
    ⟨hf.1.continuous.measurable, hf.1.continuous.bounded_above_of_compact_support hf.2.1⟩
  have hint := integral_apply_eq_of_coordMeasure_eq (sMeas u) S (topKIdx d) (topKIdx d) hm hC
    (by ext E hE; simp only [coordMeasure_apply]; rw [happ E hE, sMeas_apply_top hui hE])
    (euclideanVariation_le_of_forall _ fun E hE => by
      rw [piEuclideanNorm_topKVec, sMeas_apply_top hui hE, ← happ E hE]
      exact ofReal_abs_top_le E)
  rw [hint, sMeas_integral_top hui hm hC]
  exact ((usharp_isMetricCurrent hui).2.2.2.1 f (isBddLipFun_of_test hf)).symm

/-- Clause (3) of `flat_main`: metric currents agreeing on `(f, x)` for test
functions `f` coincide. -/
theorem flat_uniqueness {T₁ T₂ : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ}
    (h₁ : IsMetricCurrent d T₁) (h₂ : IsMetricCurrent d T₂)
    (h : ∀ f, IsTestFunctionOn Set.univ f → T₁ f (fun i x => x i) = T₂ f (fun i x => x i)) :
    ∀ f, IsBddLipFun f → ∀ π : Fin d → Vec d → ℝ, (∀ i, IsLipFun (π i)) → T₁ f π = T₂ f π := by
  obtain ⟨ν₁, hν₁, -⟩ := nu_main h₁
  obtain ⟨ν₂, hν₂, -⟩ := nu_main h₂
  obtain ⟨u₁, hu₁, -, -, hrep₁, -⟩ := usharp_of_curr_ac h₁ (fun _ hμ => curr_ac h₁ hμ) hν₁
  obtain ⟨u₂, hu₂, -, -, hrep₂, -⟩ := usharp_of_curr_ac h₂ (fun _ hμ => curr_ac h₂ hμ) hν₂
  have hae : u₁ =ᵐ[volume] u₂ := by
    have hw := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (f := u₁ - u₂)
      (hu₁.sub hu₂).locallyIntegrable fun g hg hgc => by
        have hf : IsTestFunctionOn Set.univ g := ⟨hg, hgc, Set.subset_univ _⟩
        have hgi : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hgc
        have e := h g hf
        rw [current_coord_eq hu₁ hrep₁ (isBddLipFun_of_test hf),
          current_coord_eq hu₂ hrep₂ (isBddLipFun_of_test hf)] at e
        have hI : ∀ w : Vec d → ℝ, Integrable w volume → Integrable (fun x => g x * w x) volume := by
          intro w hw
          obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
          exact hw.bdd_mul (c := C) hg.continuous.aestronglyMeasurable
            (Eventually.of_forall fun x => by simpa using hC x)
        simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
        rw [integral_sub (hI _ hu₁) (hI _ hu₂), e, sub_self]
    filter_upwards [hw] with x hx
    exact sub_eq_zero.1 hx
  intro f hf π hπ
  rw [hrep₁ f hf π hπ, hrep₂ f hf π hπ]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

end AFree
