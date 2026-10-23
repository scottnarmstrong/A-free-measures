module

public import AFree.MetricCurrents.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Locally uniform convergence of equi-Lipschitz sequences
-/

@[expose] public section

open Filter Topology
open scoped NNReal

namespace AFree

open PDE

/-- If `F n` are Euclidean `C`-Lipschitz and `F n → F` pointwise then `F` is
`C`-Lipschitz and `F n → F` uniformly on every bounded set. -/
theorem locunif {d : ℕ} {C : ℝ≥0} {F : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (hF : ∀ n, IsEuclLipschitzWith C (F n)) (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    IsEuclLipschitzWith C f ∧ ∀ B : Set (Vec d), Bornology.IsBounded B →
      TendstoUniformlyOn F f atTop B := by
  have hCf : IsEuclLipschitzWith C f := by
    intro x y
    have h1 : Tendsto (fun n => |F n x - F n y|) atTop (𝓝 |f x - f y|) :=
      ((hlim x).sub (hlim y)).abs
    exact le_of_tendsto h1 (Eventually.of_forall fun n => hF n x y)
  refine ⟨hCf, fun B hB => ?_⟩
  have hsup : ∀ g : Vec d → ℝ, IsEuclLipschitzWith C g → ∀ x y : Vec d,
      |g x - g y| ≤ (C * Real.sqrt d) * dist x y := by
    intro g hg x y
    refine (hg x y).trans ?_
    rw [mul_assoc, dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (vecEuclideanNorm_le_sqrt_natCast_mul_norm _) (NNReal.coe_nonneg _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set L : ℝ := C * Real.sqrt d with hL
  have hL0 : 0 ≤ L := mul_nonneg (NNReal.coe_nonneg _) (Real.sqrt_nonneg _)
  set η : ℝ := ε / (3 * (L + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hLη : L * η < ε / 3 := by
    rw [hη, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨t, htK, htfin, hcov⟩ := (hB.isCompact_closure).finite_cover_balls hη0
  have hev : ∀ᶠ n in atTop, ∀ y ∈ t, dist (f y) (F n y) < ε / 3 := by
    rw [htfin.eventually_all]
    intro y _
    have := Metric.tendsto_nhds.1 (hlim y) (ε / 3) (by positivity)
    filter_upwards [this] with n hn
    rwa [dist_comm]
  filter_upwards [hev] with n hn x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.1 (hcov (subset_closure hx))
  have hxy' : dist x y < η := hxy
  have a1 := hsup (F n) (hF n) x y
  have a2 := hsup f hCf x y
  have a3 := hn y hyt
  rw [Real.dist_eq] at a3 ⊢
  have b1 : L * dist x y ≤ L * η := mul_le_mul_of_nonneg_left hxy'.le hL0
  rw [abs_lt] at a3 ⊢
  rw [abs_le] at a1 a2
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

end AFree
