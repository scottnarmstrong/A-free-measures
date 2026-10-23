module

public import AFree.Curves.Rainwater.GkMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Topology of `𝒢(C)` and `𝒢_k`
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal BoundedContinuousFunction

namespace AFree

open PDE

variable {d : ℕ}

private lemma continuous_normEval (s s' : I) :
    Continuous fun γ : C(I, Vec d) => vecEuclideanNorm (γ s' - γ s) :=
  PDE.continuous_vecEuclideanNorm.comp
    ((continuous_eval_const s').sub (continuous_eval_const s))

private lemma continuous_dotEval (e : Vec d) (s s' : I) :
    Continuous fun γ : C(I, Vec d) => vecDot (γ s' - γ s) e :=
  (Curves.continuous_vecDot_left e).comp
    ((continuous_eval_const s').sub (continuous_eval_const s))

lemma isClosed_ccurveSpace (e : Vec d) (α : ℝ) : IsClosed (ccurveSpace e α) := by
  have : ccurveSpace e α = ⋂ (s : I) (s' : I) (_ : s ≤ s'),
      ({γ : C(I, Vec d) | vecEuclideanNorm (γ s' - γ s) ≤ (s' : ℝ) - s} ∩
        {γ | Real.cos α * ((s' : ℝ) - s) ≤ vecDot (γ s' - γ s) e}) := by
    ext γ; simp only [ccurveSpace, mem_ofPred_eq, mem_iInter, mem_inter_iff]
  rw [this]
  refine isClosed_iInter fun s => isClosed_iInter fun s' => isClosed_iInter fun _ => ?_
  exact (isClosed_le (continuous_normEval s s') continuous_const).inter
    (isClosed_le continuous_const (continuous_dotEval e s s'))

lemma isClosed_ccurveSpaceK (e : Vec d) (α : ℝ) (k : ℕ) : IsClosed (ccurveSpaceK e α k) := by
  have h2 : IsClosed {γ : C(I, Vec d) | ∃ s : I, vecEuclideanNorm (γ s) ≤ k} := by
    have : {γ : C(I, Vec d) | ∃ s : I, vecEuclideanNorm (γ s) ≤ k} =
        Prod.fst '' {p : C(I, Vec d) × I | vecEuclideanNorm (p.1 p.2) ≤ k} := by
      ext γ; simp
    rw [this]
    exact isClosedMap_fst_of_compactSpace _ (isClosed_le
      (PDE.continuous_vecEuclideanNorm.comp continuous_eval) continuous_const)
  exact (isClosed_ccurveSpace e α).inter h2

lemma isCompact_ccurveSpaceK (e : Vec d) (α : ℝ) (k : ℕ) : IsCompact (ccurveSpaceK e α k) := by
  set Φ := ContinuousMap.isometryEquivBoundedOfCompact I (Vec d) with hΦ
  set A : Set (I →ᵇ Vec d) := Φ '' ccurveSpaceK e α k with hA
  have hAc : IsClosed A := Φ.toHomeomorph.isClosedMap _ (isClosed_ccurveSpaceK e α k)
  have hcomp : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : Vec d) (k + 1))
      (isCompact_closedBall _ _) A ?_ ?_
    · rintro f x ⟨γ, hγ, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact (norm_le_vecEuclideanNorm _).trans (ccurveSpaceK_norm_le hγ x)
    · refine (LipschitzWith.uniformEquicontinuous (fun f : A => ((f : I →ᵇ Vec d) : I → Vec d)) 1
        ?_).equicontinuous
      rintro ⟨_, γ, hγ, rfl⟩
      refine LipschitzWith.of_dist_le_mul fun s s' => ?_
      have h1 := ccurveSpace_dist_le hγ.1 s s'
      have h3 := norm_le_vecEuclideanNorm (γ s' - γ s)
      show dist (γ s) (γ s') ≤ _
      simp only [dist_eq_norm, NNReal.coe_one, one_mul, Subtype.dist_eq, Real.norm_eq_abs]
      rw [norm_sub_rev, abs_sub_comm]
      linarith
  rw [hAc.closure_eq] at hcomp
  have := hcomp.image Φ.symm.continuous
  rwa [hA, ← image_comp, Φ.symm_comp_self, image_id] at this

/-- The evaluation `(γ, s) ↦ γ(s)` is continuous on `𝒢(C) × [0,1]`. -/
lemma continuous_ccurveSpace_eval (e : Vec d) (α : ℝ) :
    Continuous fun p : ccurveSpace e α × I => (p.1 : C(I, Vec d)) p.2 :=
  continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)

end AFree
