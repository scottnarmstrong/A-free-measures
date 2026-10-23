module

public import AFree.Curves.Perturb.Nbhd
public import AFree.Curves.Perturb.GDef

/-!
# The reverse Fatou contradiction
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ}

/-- If `K` is compact and `C(e, α)`-null, there are no
`tan α`-Lipschitz maps `ζ_n → ζ₀` pointwise on `[u₀, u₁]` into `e^⊥` and radii `δ_n → 0` with
`𝓛¹{u ∈ [u₀, u₁] : γ_{ζ_n}(u) ∈ N_{δ_n}(K)} ≥ ε > 0` for all `n`. -/
theorem perturb_step1_limsup_contradiction (he : vecEuclideanNorm e = 1) (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {K : Set (Vec d)} (hK : IsCompact K) (hnull : IsCNull (cone e α) K)
    {u₀ u₁ ε : ℝ} (hu : u₀ ≤ u₁) (hε : 0 < ε) {ζ : ℕ → ℝ → Vec d} {ζ₀ : ℝ → Vec d}
    (hζ : ∀ n, IsConeGraphFn e α u₀ u₁ (ζ n)) (hζ₀ : IsConeGraphFn e α u₀ u₁ ζ₀)
    (hconv : ∀ u ∈ Icc u₀ u₁, Tendsto (fun n => ζ n u) atTop (𝓝 (ζ₀ u)))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hmeas : ∀ n, ENNReal.ofReal ε ≤ perturbMeas e (perturbClosedNbhd K (δ n)) u₀ u₁ (ζ n)) :
    False := by
  have htan : 0 ≤ Real.tan α := (Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2).le
  set S : ℕ → Set ℝ := fun n =>
    Icc u₀ u₁ ∩ {u | graphCurve e (ζ n) u ∈ perturbClosedNbhd K (δ n)} with hS
  have hSclosed : ∀ n, IsClosed (S n) := fun n =>
    ((hζ n).continuousOn_graphCurve htan).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_perturbClosedNbhd hK (δ n))
  have hSsub : ∀ n, S n ⊆ Icc u₀ u₁ := fun n => inter_subset_left
  set T : ℕ → Set ℝ := fun m => ⋃ n, S (m + n) with hT
  have hTanti : Antitone T := by
    intro m m' hmm' u hu
    obtain ⟨n, hn⟩ := mem_iUnion.mp hu
    exact mem_iUnion.mpr ⟨n + (m' - m), by
      have : m + (n + (m' - m)) = m' + n := by omega
      rw [this]; exact hn⟩
  have hTmeas : ∀ m, NullMeasurableSet (T m) volume := fun m =>
    (MeasurableSet.iUnion fun n => (hSclosed (m + n)).measurableSet).nullMeasurableSet
  have hTfin : ∃ m, volume (T m) ≠ ⊤ := ⟨0, ne_of_lt ((measure_mono
    (iUnion_subset fun n => hSsub (0 + n))).trans_lt measure_Icc_lt_top)⟩
  have hlim := tendsto_measure_iInter_atTop hTmeas hTanti hTfin
  have hZ : ENNReal.ofReal ε ≤ volume (⋂ m, T m) := by
    refine ge_of_tendsto' hlim fun m => ?_
    exact (hmeas m).trans (measure_mono (subset_iUnion (fun n => S (m + n)) 0))
  have hZsub : (⋂ m, T m) ⊆ Icc u₀ u₁ ∩ graphCurve e ζ₀ ⁻¹' K := by
    intro u hu
    have hu' : ∀ m, ∃ n, u ∈ S (m + n) := fun m => mem_iUnion.mp (mem_iInter.mp hu m)
    obtain ⟨n0, hn0⟩ := hu' 0
    have huI : u ∈ Icc u₀ u₁ := hSsub _ hn0
    refine ⟨huI, ?_⟩
    rw [mem_preimage, ← hK.isClosed.closure_eq, Metric.mem_closure_iff]
    intro r hr
    have h1 : ∀ᶠ n in atTop, δ n < r / 2 := hδ.eventually (gt_mem_nhds (half_pos hr))
    have h2 : ∀ᶠ n in atTop, dist (ζ n u) (ζ₀ u) < r / 2 :=
      (Metric.tendsto_nhds.mp (hconv u huI)) _ (half_pos hr)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h1.and h2)
    obtain ⟨n, hn⟩ := hu' N
    obtain ⟨hN1, hN2⟩ := hN (N + n) (by omega)
    obtain ⟨-, k, hk, hk2⟩ := hn
    refine ⟨k, hk, ?_⟩
    have e1 : graphCurve e ζ₀ u - graphCurve e (ζ (N + n)) u = ζ₀ u - ζ (N + n) u := by
      simp [graphCurve]
    have e2 := norm_le_vecEuclideanNorm (graphCurve e (ζ (N + n)) u - k)
    have e3 : ‖graphCurve e ζ₀ u - graphCurve e (ζ (N + n)) u‖ < r / 2 := by
      rw [e1, ← dist_eq_norm, dist_comm]; exact hN2
    rw [dist_eq_norm]
    have : graphCurve e ζ₀ u - k = (graphCurve e ζ₀ u - graphCurve e (ζ (N + n)) u) +
        (graphCurve e (ζ (N + n)) u - k) := by abel
    rw [this]
    refine (norm_add_le _ _).trans_lt ?_
    linarith
  have hzero := ((graphform_comparison_and_null_iff he hα hα2).2 K).mp hnull u₀ u₁ ζ₀ hu hζ₀
  have := (hZ.trans (measure_mono hZsub)).trans_eq hzero
  exact absurd this (not_le.mpr (ENNReal.ofReal_pos.mpr hε))

end AFree
