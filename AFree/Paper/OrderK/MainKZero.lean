module

public import AFree.Paper.OrderK.Blow
public import AFree.Measure.DimZero

/-!
# The cases `d = 0` and `k = 0`

The degenerate cases `d = 0` and `k = 0` of the main theorem.
-/

@[expose] public section

open MeasureTheory Matrix PDE

namespace AFree

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- If `d = 0`, `σˢ = 0` for every finite measure `σ` on `ℝ⁰`; hence the main
theorem holds for `d = 0`. -/
theorem lem_dzerok (σ : Measure (Vec 0)) [IsFiniteMeasure σ] :
    σ.singularPart volume = 0 :=
  singularPart_eq_zero_dimZero σ

/-- For `k = 0`, `d ≥ 1` and `(σ, P)` `A`-free in `Ω` with `A₀` smooth on `Ω`:
`A₀(x) P(x) = 0` for `σ`-a.e. `x ∈ Ω`; hence `P(x) ∈ Λ^{(0)}_{A(x)} = ker A₀(x)` for `σˢ`-a.e. `x`. -/
theorem lem_kzero {d : ℕ} (hd : 0 < d) {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω)
    (σ : Measure (Vec d)) [IsFiniteMeasure σ] {P : Vec d → ι → ℝ}
    (hPi : Integrable P σ) (h : IsFreePairVar Ω 0 A σ P) :
    (∀ᵐ x ∂σ, x ∈ Ω → A 0 x *ᵥ P x = 0) ∧
      ∀ᵐ x ∂σ.singularPart volume, P x ∈ waveCone 0 (fun α => A α x) := by
  have hPc : ∀ i, Integrable (fun x => P x i) σ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hPi
  have hint : ∀ j, ∀ U : Set (Vec d), IsOpen U → IsCompact (closure U) → closure U ⊆ Ω →
      IntegrableOn (fun x => ∑ i, A 0 x j i * P x i) U σ := by
    intro j U _ hUc hUΩ
    refine IntegrableOn.mono_set ?_ subset_closure
    refine integrable_finsetSum _ fun i _ => ?_
    exact IntegrableOn.continuousOn_mul ((hA 0 j i).continuousOn.mono hUΩ)
      (hPc i).integrableOn hUc
  have hz : ∀ j, ∀ᵐ x ∂σ, x ∈ Ω → ∑ i, A 0 x j i * P x i = 0 := by
    intro j
    refine lem_measuniq hΩ σ (hint j) fun φ hφ => ?_
    have := h.2 φ hφ j
    rw [Finset.range_one, Finset.sum_singleton, Finset.Nat.antidiagonalTuple_zero_right,
      Finset.sum_singleton] at this
    refine Eq.trans ?_ this
    rw [pow_zero, one_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show φ x * ∑ i, A 0 x j i * P x i =
      ∑ i, multiCoordDeriv 0 (fun z => φ z * A 0 z j i) x * P x i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [multiCoordDeriv_zero]
    ring
  have hall : ∀ᵐ x ∂σ, x ∈ Ω → A 0 x *ᵥ P x = 0 := by
    have := ae_all_iff.2 hz
    filter_upwards [this] with x hx hxΩ
    funext j
    exact hx j hxΩ
  refine ⟨hall, ?_⟩
  have hΩσ : ∀ᵐ x ∂σ, x ∈ Ω := by
    exact measure_eq_zero_iff_ae_notMem.1 h.1 |>.mono fun x hx => not_not.1 hx
  have h1 : ∀ᵐ x ∂σ, P x ∈ waveCone 0 (fun α => A α x) := by
    filter_upwards [hall, hΩσ] with x hx hxΩ
    refine ⟨basisVec ⟨0, hd⟩, vecEuclideanNorm_basisVec _, ?_⟩
    simpa [Finset.Nat.antidiagonalTuple_zero_right] using hx hxΩ
  exact Measure.absolutelyContinuous_of_le (Measure.singularPart_le σ volume) h1

end

end AFree
