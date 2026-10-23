module

public import AFree.Curves.Rainwater.Mix

/-!
# Continuity of `γ ↦ λ_γ` on `𝒢_k` and the identification of the mixtures
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal BoundedContinuousFunction

namespace AFree

open PDE

variable {d : ℕ}

/-- The closed Euclidean ball `B(k+1) ⊂ ℝ^d` carrying the measures `λ_γ`, `γ ∈ 𝒢_k`. -/
abbrev curveBall (d k : ℕ) : Set (Vec d) := euclideanClosedBall (0 : Vec d) ((k : ℝ) + 1)

instance (k : ℕ) : CompactSpace (curveBall d k) :=
  isCompact_iff_compactSpace.1 (isCompact_euclideanClosedBall (0 : Vec d) (by positivity))

instance (e : Vec d) (α : ℝ) (k : ℕ) : CompactSpace (ccurveSpaceK e α k) :=
  isCompact_iff_compactSpace.1 (isCompact_ccurveSpaceK e α k)

lemma mem_curveBall {e : Vec d} {α : ℝ} {k : ℕ} {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpaceK e α k)
    (s : I) : γ s ∈ curveBall d k := by
  rw [curveBall, mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)]
  simpa using ccurveSpaceK_norm_le hγ s

/-- `λ_γ` for `γ ∈ 𝒢_k`, as a probability measure on the compact ball `B(k+1)`. -/
noncomputable def curveLawK (e : Vec d) (α : ℝ) (k : ℕ) (γ : ccurveSpaceK e α k) :
    ProbabilityMeasure (curveBall d k) :=
  ⟨Measure.map (fun s : I => (⟨(γ : C(I, Vec d)) s, mem_curveBall γ.2 s⟩ : curveBall d k))
    volume, inferInstance⟩

lemma map_val_curveLawK (e : Vec d) (α : ℝ) (k : ℕ) (γ : ccurveSpaceK e α k) :
    Measure.map Subtype.val (curveLawK e α k γ : Measure (curveBall d k)) =
      curveLaw (γ : C(I, Vec d)) := by
  have hc : Continuous fun s : I => (⟨(γ : C(I, Vec d)) s, mem_curveBall γ.2 s⟩ : curveBall d k) :=
    (γ : C(I, Vec d)).continuous.subtype_mk _
  change Measure.map Subtype.val (Measure.map _ volume) = _
  rw [Measure.map_map continuous_subtype_val.measurable hc.measurable]
  rfl

/-- (a) `γ ↦ λ_γ` is continuous from `𝒢_k` to `𝒫(B(k+1))` (weak topology). -/
theorem continuous_curveLawK (e : Vec d) (α : ℝ) (k : ℕ) : Continuous (curveLawK e α k) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hc : ∀ γ : ccurveSpaceK e α k,
      Continuous fun s : I => (⟨(γ : C(I, Vec d)) s, mem_curveBall γ.2 s⟩ : curveBall d k) :=
    fun γ => (γ : C(I, Vec d)).continuous.subtype_mk _
  have key : ∀ γ : ccurveSpaceK e α k, ∫ x, f x ∂(curveLawK e α k γ : Measure (curveBall d k)) =
      ∫ s : I, f ⟨(γ : C(I, Vec d)) s, mem_curveBall γ.2 s⟩ := fun γ =>
    integral_map (hc γ).measurable.aemeasurable f.continuous.aestronglyMeasurable
  simp_rw [key]
  refine continuous_of_dominated (bound := fun _ => ‖f‖) (fun γ => ?_) (fun γ => ?_) ?_ ?_
  · exact ((f.continuous.comp (hc γ)).aestronglyMeasurable)
  · exact Eventually.of_forall fun s => f.norm_coe_le_norm _
  · exact integrable_const _
  · refine Eventually.of_forall fun s => f.continuous.comp ?_
    exact ((continuous_eval_const s).comp continuous_subtype_val).subtype_mk _

/-- For `Y = 𝒢_k`, `Φ(γ) = λ_γ`: the pushforward of `[τ]_Φ` to `ℝ^d` is `[τ]`. -/
theorem map_val_mixMeasure_curveLawK (e : Vec d) (α : ℝ) (k : ℕ) (τ : Measure (ccurveSpaceK e α k)) :
    Measure.map Subtype.val (mixMeasure (curveLawK e α k) τ) = curveMix (ccurveSpaceK e α k) τ := by
  refine Measure.ext fun E hE => ?_
  have hΦ := continuous_curveLawK e α k
  rw [Measure.map_apply continuous_subtype_val.measurable hE,
    mixMeasure_apply hΦ _ (continuous_subtype_val.measurable hE), curveMix_apply _ _ hE]
  refine lintegral_congr fun γ => ?_
  rw [← map_val_curveLawK, Measure.map_apply continuous_subtype_val.measurable hE]

end AFree
