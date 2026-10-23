module

public import AFree.Paper.OrderK.MainBlow
public import AFree.Paper.OrderK.MainKZero

/-!
# The main theorem for operators of every order

[DPR, Theorem 1.1] for operators of every order, first for pairs `(σ, P)` with variable coefficients.
-/

@[expose] public section

open MeasureTheory Matrix PDE

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- If `(σ, P)` is `A`-free in `Ω` (variable coefficients smooth on `Ω`), then
`P(x) ∈ Λ_x = Λ^{(k)}_{A(x)}` for `σˢ`-a.e. `x`. -/
theorem thm_main_pair {k : ℕ} {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω)
    (σ : Measure (Vec d)) [IsFiniteMeasure σ] {P : Vec d → ι → ℝ} (hPm : Measurable P)
    (hPi : Integrable P σ) (h : IsFreePairVar Ω k A σ P) :
    ∀ᵐ x ∂σ.singularPart volume, P x ∈ waveCone k (fun α => A α x) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have := lem_dzerok σ
    rw [this]
    simp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (lem_kzero hd hΩ hA σ hPi h).2
  rw [ae_iff]
  refine le_antisymm ?_ bot_le
  have hsub : {x | ¬ P x ∈ waveCone k (fun α => A α x)} ⊆ badSetK Ω k A P ∪ Ωᶜ := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · exact Or.inl ⟨hxΩ, hx⟩
    · exact Or.inr hxΩ
  have h1 := thm_main_pair_blowup hd hk hΩ hA σ hPm hPi h
  have h2 : σ.singularPart volume Ωᶜ = 0 :=
    le_antisymm ((Measure.le_iff'.1 (Measure.singularPart_le σ volume) Ωᶜ).trans h.1.le) bot_le
  calc σ.singularPart volume {x | ¬ P x ∈ waveCone k (fun α => A α x)}
      ≤ σ.singularPart volume (badSetK Ω k A P ∪ Ωᶜ) := measure_mono hsub
    _ ≤ σ.singularPart volume (badSetK Ω k A P) + σ.singularPart volume Ωᶜ := measure_union_le _ _
    _ = 0 := by rw [h1, h2, add_zero]

/-- [DPR, Theorem 1.1] for operators of every order `k`: for an `𝒜`-free vector measure with
`|μ|(Ωᶜ) = 0` and constant coefficients, `polar μ ∈ Λ_𝒜` at `|μ|ˢ`-a.e. point. -/
theorem thm_general {k : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFree Ω k A μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveCone k A := by
  obtain ⟨hfin, hm, hi, -, hb⟩ := lem_varpair (κ := κ) hΩ k μ
  have hpair : IsFreePairVar Ω k (fun α (_ : Vec d) => A α) (euclideanVariation μ) (polar μ) :=
    (hb A hμ hfree).2
  have key := thm_main_pair (k := k) (A := fun α (_ : Vec d) => A α) hΩ
    (fun α j i => contDiffOn_const) (euclideanVariation μ) hm hi hpair
  exact key

end

end AFree
