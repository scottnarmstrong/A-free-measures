module

public import AFree.TopCurrents.Assembly.FlatBd
public import AFree.TopCurrents.Assembly.CurrAC
public import AFree.TopCurrents.Representation
public import AFree.TopCurrents.SmoothDense
public import AFree.TopCurrents.USharpMain

/-!
# [DPR, Theorem 1.15]: flat-chain identification, clauses (1) and (2)(i) of `flat_main`
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.Nu

variable {d : ℕ}

private lemma measurable_bdd_of_test {f : Vec d → ℝ} (hf : IsTestFunctionOn Set.univ f) :
    Measurable f ∧ ∃ C, ∀ x, ‖f x‖ ≤ C :=
  ⟨hf.1.continuous.measurable, hf.1.continuous.bounded_above_of_compact_support hf.2.1⟩

private lemma test_integrable {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Set.univ φ) :
    Integrable φ volume := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1

private lemma coord_isLipTuple : IsLipTuple (coordTuple d) := fun i => ⟨1, coord_lip i⟩

/-- `T f x = ∫ f u` for `T = u_#`-represented currents and `f ∈ Lip_b`. -/
lemma current_coord_eq {T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ} {u : Vec d → ℝ}
    (hui : Integrable u volume)
    (hrep : ∀ f, IsBddLipFun f → ∀ π : Fin d → Vec d → ℝ, IsLipTuple π →
      T f π = ∫ x, f x * u x * jacDet π x) {f : Vec d → ℝ} (hf : IsBddLipFun f) :
    T f (fun i x => x i) = ∫ x, f x * u x := by
  have h1 := hrep f hf (coordTuple d) coord_isLipTuple
  have h2 := (usharp_isMetricCurrent hui).2.2.2.1 f hf
  exact h1.trans h2

/-- Clause (1) of `flat_main`: a compactly supported metric current is `T̃ = u 𝓛^d e_top`
for a flat chain. -/
theorem flat_current_to_chain {T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent d T) (hK : HasCompactAKSupport T) :
    ∃ S, IsTopFlatChain S ∧ ∀ f, IsTestFunctionOn Set.univ f →
      (∫ᵛ x, f x ∂•S) (topKIdx d) = T f (fun i x => x i) := by
  obtain ⟨ν, hν, -⟩ := nu_main hT
  obtain ⟨u, hui, hνu, -, hrep, hmass⟩ := usharp_of_curr_ac hT (fun _ hμ => curr_ac hT hμ) hν
  obtain ⟨K, hKc, hKm⟩ := hK
  have hKu : uMass u Kᶜ = 0 := hKm _ hmass
  refine ⟨sMeas u, ⟨⟨K, hKc, le_antisymm ?_ bot_le⟩, fun ε hε => ?_⟩, fun f hf => ?_⟩
  · exact ((euclideanVariation_le_uMass hui _ fun _ hE => sMeas_apply_top hui hE) _).trans hKu.le
  · obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
    have hrpos : (0 : ℝ) < r := NNReal.coe_pos.2 (ENNReal.coe_pos.1 hr0)
    obtain ⟨φ, hφ, hφint⟩ := smoothdense hui hrpos
    have hφi := test_integrable hφ
    refine ⟨sMeas φ, ⟨by simp, _, isBoundaryOn_sMeas hφ⟩,
      ⟨tsupport φ, hφ.2.1, le_antisymm ?_ bot_le⟩, ?_⟩
    · refine ((euclideanVariation_le_uMass hφi _ fun _ hE => sMeas_apply_top hφi hE) _).trans
        (uMass_compl_eq_zero (isClosed_tsupport φ).measurableSet
          (Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx)).le
    · refine ((euclideanVariation_le_uMass (hui.sub hφi) _ fun _ hE =>
        sMeas_sub_apply_top hui hφi hE) _).trans_lt ?_
      rw [uMass_univ (hui.sub hφi)]
      calc ENNReal.ofReal (∫ x, |(u - φ) x|) < ENNReal.ofReal r :=
            (ENNReal.ofReal_lt_ofReal_iff hrpos).2 (by simpa using hφint)
        _ = r := ENNReal.ofReal_coe_nnreal
        _ < ε := hrε
  · obtain ⟨hm, C, hC⟩ := measurable_bdd_of_test hf
    rw [sMeas_integral_top hui hm hC, current_coord_eq hui hrep (isBddLipFun_of_test hf)]

end AFree
