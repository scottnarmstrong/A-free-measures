module

public import AFree.Rademacher.Chain.PertCone
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# The Besicovitch covering of the single-stage perturbation

The Besicovitch covering step in the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- A positive gap between finitely many pairwise disjoint closed balls. -/
theorem exists_gap_closedBalls (T : Finset (Vec d)) (r : Vec d → ℝ)
    (hdis : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → r p + r q < dist p q) :
    ∃ η : ℝ, 0 < η ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → r p + r q + η < dist p q := by
  have h : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ p ∈ T, ∀ q ∈ T, p ≠ q → r p + r q + η < dist p q := by
    rw [Filter.eventually_all_finset]
    intro p hp
    rw [Filter.eventually_all_finset]
    intro q hq
    by_cases hpq : p = q
    · exact Filter.Eventually.of_forall fun _ h => absurd hpq h
    · have hcont : ContinuousAt (fun η : ℝ => r p + r q + η) 0 := by fun_prop
      have : ∀ᶠ η in 𝓝 (0 : ℝ), r p + r q + η < dist p q :=
        hcont.eventually_lt continuousAt_const (by simpa using hdis p hp q hq hpq)
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun η h _ => h
  obtain ⟨η, hη, hη0⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨η, hη0, hη⟩

/-- Besicovitch step: a finite family of points of `S`
with radii `ρ < R` (and enlarged radii `ρ' ∈ (ρ, 2ρ]` with pairwise disjoint closed balls) and
compact sets `K p ⊆ S ∩ B̄(p, ρ p)` carrying a property `P`, whose union has measure at least
`μ S / 4`. -/
theorem pert_covering (μ : Measure (Vec d)) [IsFiniteMeasure μ] {S : Set (Vec d)}
    (hS : MeasurableSet S) {R : Vec d → ℝ} (hR : ∀ p ∈ S, 0 < R p)
    (P : Vec d → ℝ → Set (Vec d) → Prop)
    (hK : ∀ p ∈ S, ∀ r, 0 < r → r < R p → ∃ K ⊆ S ∩ closedBall p r, IsCompact K ∧ P p r K ∧
      μ (S ∩ closedBall p r) ≤ 2 * μ K) :
    ∃ (T : Finset (Vec d)) (ρ ρ' : Vec d → ℝ) (K : Vec d → Set (Vec d)),
      (∀ p ∈ T, p ∈ S ∧ 0 < ρ p ∧ ρ p < R p ∧ ρ p < ρ' p ∧ ρ' p ≤ 2 * ρ p ∧
        K p ⊆ S ∩ closedBall p (ρ p) ∧ IsCompact (K p) ∧ P p (ρ p) (K p)) ∧
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → Disjoint (closedBall p (ρ' p)) (closedBall q (ρ' q))) ∧
      μ S ≤ 4 * μ (⋃ p ∈ T, K p) := by
  obtain ⟨t, r, htc, htS, htr, hnull, hdisj⟩ := Besicovitch.exists_disjoint_closedBall_covering_ae
    μ (fun _ => (univ : Set ℝ)) S (fun x _ δ hδ => ⟨δ / 2, mem_univ _, by constructor <;> linarith⟩)
    R hR
  have hKex : ∀ p : Vec d, ∃ K : Set (Vec d), p ∈ t → (K ⊆ S ∩ closedBall p (r p) ∧
      IsCompact K ∧ P p (r p) K ∧ μ (S ∩ closedBall p (r p)) ≤ 2 * μ K) := by
    intro p
    by_cases hp : p ∈ t
    · obtain ⟨K, h1, h2, h3, h4⟩ := hK p (htS hp) (r p) (htr p hp).2.1 (htr p hp).2.2
      exact ⟨K, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨∅, fun h => absurd h hp⟩
  choose Kf hKf using hKex
  by_cases hμS : μ S = 0
  · refine ⟨∅, r, r, Kf, by simp, by simp, by simp [hμS]⟩
  -- finite subfamily
  have hUm : MeasurableSet (⋃ p ∈ t, closedBall p (r p)) :=
    MeasurableSet.biUnion htc fun p _ => measurableSet_closedBall
  have hsplit : μ S = ∑' p : t, μ (S ∩ closedBall p (r p)) := by
    have h1 := measure_inter_add_sdiff (μ := μ) S hUm
    rw [hnull, add_zero] at h1
    rw [← h1, inter_iUnion₂]
    exact measure_biUnion htc (hdisj.mono (fun p => Set.inter_subset_right))
      fun p _ => hS.inter measurableSet_closedBall
  have hlt : μ S / 2 < ∑' p : t, μ (S ∩ closedBall p (r p)) := by
    rw [← hsplit]
    exact ENNReal.half_lt_self hμS (measure_ne_top μ S)
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hlt
  obtain ⟨T0, hT0⟩ := hlt
  set T : Finset (Vec d) := T0.image Subtype.val with hT
  have hTt : ∀ p ∈ T, p ∈ t := by
    intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hp
    exact q.2
  have hsumT : ∑ p ∈ T0, μ (S ∩ closedBall (p : Vec d) (r p)) =
      ∑ p ∈ T, μ (S ∩ closedBall p (r p)) :=
    (Finset.sum_image (f := fun p => μ (S ∩ closedBall p (r p))) (fun a _ b _ h => Subtype.ext h)).symm
  -- disjointness data
  have hdr : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → r p + r q < dist p q := by
    intro p hp q hq hpq
    have := hdisj (hTt p hp) (hTt q hq) hpq
    rwa [Function.onFun, disjoint_closedBall_closedBall_iff (htr p (hTt p hp)).2.1.le
      (htr q (hTt q hq)).2.1.le] at this
  obtain ⟨η, hη, hηd⟩ := exists_gap_closedBalls T r hdr
  set ρ' : Vec d → ℝ := fun p => r p + min (r p) (η / 3) with hρ'
  have hρpos : ∀ p ∈ T, 0 < r p := fun p hp => (htr p (hTt p hp)).2.1
  refine ⟨T, r, ρ', Kf, fun p hp => ?_, fun p hp q hq hpq => ?_, ?_⟩
  · have hpt := hTt p hp
    obtain ⟨h1, h2, h3, -⟩ := hKf p hpt
    refine ⟨htS hpt, hρpos p hp, (htr p hpt).2.2, ?_, ?_, h1, h2, h3⟩
    · have : 0 < min (r p) (η / 3) := lt_min (hρpos p hp) (by linarith)
      simp only [hρ']; linarith
    · simp only [hρ']; linarith [min_le_left (r p) (η / 3)]
  · have hpos' : ∀ p ∈ T, 0 ≤ ρ' p := by
      intro p hp
      have := lt_min (hρpos p hp) (by linarith : 0 < η / 3)
      have := hρpos p hp
      simp only [hρ']; linarith
    rw [disjoint_closedBall_closedBall_iff (hpos' p hp) (hpos' q hq)]
    have := hηd p hp q hq hpq
    simp only [hρ']
    linarith [min_le_right (r p) (η / 3), min_le_right (r q) (η / 3)]
  · -- measure
    have hKdisj : (T : Set (Vec d)).PairwiseDisjoint Kf := by
      intro p hp q hq hpq
      refine (hdisj (hTt p hp) (hTt q hq) hpq).mono ?_ ?_
      · exact (hKf p (hTt p hp)).1.trans inter_subset_right
      · exact (hKf q (hTt q hq)).1.trans inter_subset_right
    rw [measure_biUnion_finset hKdisj fun p hp => (hKf p (hTt p hp)).2.1.measurableSet]
    have hle : ∑ p ∈ T, μ (S ∩ closedBall p (r p)) ≤ 2 * ∑ p ∈ T, μ (Kf p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun p hp => (hKf p (hTt p hp)).2.2.2
    have h2 : μ S / 2 ≤ 2 * ∑ p ∈ T, μ (Kf p) := by
      rw [hsumT] at hT0
      exact hT0.le.trans hle
    calc μ S = 2 * (μ S / 2) := by rw [ENNReal.mul_div_cancel (by simp) (by simp)]
      _ ≤ 2 * (2 * ∑ p ∈ T, μ (Kf p)) := by gcongr
      _ = 4 * ∑ p ∈ T, μ (Kf p) := by rw [← mul_assoc]; norm_num

end AFree.Rademacher
