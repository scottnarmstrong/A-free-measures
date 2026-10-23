module

public import AFree.Curves.Perturb.Step1Compact
public import AFree.Curves.Perturb.Step1Limsup
public import AFree.Curves.Perturb.Step1Reduce

/-!
# Uniform smallness near a `C`-null compact set
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ}

/-- Let `K` be a compact `C(e, α)`-null set and `ε > 0`. There is
`δ ∈ (0, 1]` such that for every `tan α`-Lipschitz `η : [a, b] → e^⊥`,
`𝓛¹{u ∈ [a, b] : dist(γ_η(u), K) ≤ δ} ≤ ε` (Euclidean distance; the set is
`perturbClosedNbhd K δ`, the measure is `perturbMeas`). -/
theorem perturb_step1 (he : vecEuclideanNorm e = 1) (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {K : Set (Vec d)} (hK : IsCompact K) (hnull : IsCNull (cone e α) K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ a b η, IsConeGraphFn e α a b η →
      perturbMeas e (perturbClosedNbhd K δ) a b η ≤ ENNReal.ofReal ε := by
  have htan : 0 ≤ Real.tan α := (Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2).le
  by_contra H
  push Not at H
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_vecEuclideanNorm.continuousOn
  set R : ℝ := max C 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ k ∈ K, vecEuclideanNorm k ≤ R := fun k hk =>
    ((le_abs_self _).trans (by simpa using hC k hk)).trans (le_max_left _ _)
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδ1 : ∀ n, δ n ≤ 1 := fun n =>
    div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
  choose a b η hη hlt using fun n => H (δ n) (hδpos n) (hδ1 n)
  have hab : ∀ n, a n ≤ b n := by
    intro n
    by_contra h
    push Not at h
    have : perturbMeas e (perturbClosedNbhd K (δ n)) (a n) (b n) (η n) = 0 := by
      unfold perturbMeas
      rw [Icc_eq_empty (not_le.mpr h)]; simp
    have h2 := hlt n
    rw [this] at h2
    exact not_lt_zero h2
  choose ζ hζ hζu hζm using fun n =>
    perturb_step1_reduction he htan hR0 hR (hδ1 n) (hab n) (hη n)
  have hM : ∀ n, ∃ u ∈ Icc (-R - 1) (R + 1), vecEuclideanNorm (ζ n u) ≤ 2 * R + 2 := by
    intro n
    have hne : (Icc (a n) (b n) ∩ {u | graphCurve e (η n) u ∈
        perturbClosedNbhd K (δ n)}).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      have h2 := hlt n
      unfold perturbMeas at h2
      rw [h] at h2
      simp at h2
    obtain ⟨u, hu, hP⟩ := hne
    obtain ⟨hJ, hz, hn⟩ := hζu n u hu hP
    exact ⟨u, hJ, by rw [hz]; exact hn⟩
  obtain ⟨φ, ζ₀, hφ, hζ₀, hconv⟩ := perturb_step1_compactness htan hζ hM
  have hδt : Tendsto (fun n => δ (φ n)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  exact perturb_step1_limsup_contradiction he hα hα2 hK hnull (by linarith) hε
    (fun n => hζ (φ n)) hζ₀ hconv hδt
    (fun n => ((hlt (φ n)).trans_le (hζm (φ n))).le)

end AFree
