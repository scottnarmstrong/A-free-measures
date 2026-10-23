module

public import AFree.Curves.Rainwater

/-!
# Set-up for the dichotomy: annuli and the restricted measures `μ_k`

The annuli `𝒜_0 = B(0)`,
`𝒜_{k+1} = B(k+1) ∖ B(k)` form a Borel partition of `ℝ^d` with `𝒜_k ⊆ B(k)`; `μ_k = μ⌞(F ∩ 𝒜_k)`
is viewed as a finite Borel measure on the compact ball `X_k = B(k+1)` (`curveBall d k`).
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The Borel partition `𝒜_0 = B(0)`, `𝒜_{k+1} = B(k+1) ∖ B(k)` of `ℝ^d`. -/
def dichAnnulus (d : ℕ) : ℕ → Set (Vec d)
  | 0 => euclideanClosedBall 0 0
  | k + 1 => euclideanClosedBall 0 ((k : ℝ) + 1) \ euclideanClosedBall 0 (k : ℝ)

lemma measurableSet_dichAnnulus (k : ℕ) : MeasurableSet (dichAnnulus d k) := by
  cases k with
  | zero => exact measurableSet_euclideanClosedBall _ _
  | succ k => exact (measurableSet_euclideanClosedBall _ _).diff (measurableSet_euclideanClosedBall _ _)

lemma dichAnnulus_subset_ball (k : ℕ) : dichAnnulus d k ⊆ euclideanClosedBall 0 (k : ℝ) := by
  cases k with
  | zero => exact fun x hx => by simpa [dichAnnulus] using hx
  | succ k => exact fun x hx => by push_cast; exact hx.1

lemma dichAnnulus_subset_curveBall (k : ℕ) : dichAnnulus d k ⊆ curveBall d k :=
  (dichAnnulus_subset_ball k).trans (euclideanClosedBall_mono (Nat.cast_nonneg k) (by linarith))

lemma iUnion_dichAnnulus : ⋃ k, dichAnnulus d k = (univ : Set (Vec d)) := by
  refine eq_univ_of_forall fun x => ?_
  have hex : ∃ k : ℕ, vecEuclideanNorm x ≤ k := exists_nat_ge _
  classical
  refine mem_iUnion.2 ⟨Nat.find hex, ?_⟩
  have h1 := Nat.find_spec hex
  cases hk : Nat.find hex with
  | zero =>
    rw [hk] at h1
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le le_rfl).2 (by simpa using h1)
  | succ m =>
    rw [hk] at h1
    have h2 : ¬ vecEuclideanNorm x ≤ m := Nat.find_min hex (by omega)
    refine ⟨(mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2 (by simpa using h1),
      fun h => h2 ?_⟩
    simpa using (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).1 h

/-- `μ_k = μ⌞(F ∩ 𝒜_k)` as a measure on the ball `X_k = B(k+1)`. -/
noncomputable def dichMeasure (μ : Measure (Vec d)) (F : Set (Vec d)) (k : ℕ) :
    Measure (curveBall d k) :=
  (μ.restrict (F ∩ dichAnnulus d k)).comap Subtype.val

lemma measurableSet_curveBall (k : ℕ) : MeasurableSet (curveBall d k) :=
  measurableSet_euclideanClosedBall _ _

lemma dichMeasure_apply (μ : Measure (Vec d)) {F : Set (Vec d)} (hF : MeasurableSet F) (k : ℕ)
    (E : Set (curveBall d k)) :
    dichMeasure μ F k E = μ (Subtype.val '' E ∩ (F ∩ dichAnnulus d k)) := by
  rw [dichMeasure, (MeasurableEmbedding.subtype_coe (measurableSet_curveBall k)).comap_apply,
    Measure.restrict_apply' (hF.inter (measurableSet_dichAnnulus k))]

instance (μ : Measure (Vec d)) [IsFiniteMeasure μ] {F : Set (Vec d)} (k : ℕ) :
    IsFiniteMeasure (dichMeasure μ F k) := by
  refine ⟨?_⟩
  rw [dichMeasure, (MeasurableEmbedding.subtype_coe (measurableSet_curveBall k)).comap_apply]
  exact measure_lt_top _ _

/-- A set `W ⊆ ℝ^d` met by the support of `μ⌞F` in a null set has `μ_k(val⁻¹ W) = 0`. -/
lemma dichMeasure_preimage_null (μ : Measure (Vec d)) {F : Set (Vec d)} (hF : MeasurableSet F)
    (k : ℕ) {W : Set (Vec d)} (hW : (μ.restrict F) W = 0) :
    dichMeasure μ F k (Subtype.val ⁻¹' W) = 0 := by
  rw [dichMeasure_apply μ hF k]
  refine measure_mono_null (fun x hx => ?_) (show μ (W ∩ F) = 0 by
    rwa [Measure.restrict_apply' hF] at hW)
  obtain ⟨⟨y, hy, rfl⟩, hxF, -⟩ := hx
  exact ⟨hy, hxF⟩

end AFree
