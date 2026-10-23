module

public import AFree.Paper.OrderK.Main

/-!
# Variable coefficients (Remark 1.4)

[DPR, Remark 1.4]: the hypothesis `IsFreeVar` only constrains
`A_α` for `|α| ≤ k`, so the coefficients are first truncated to those indices; the truncation does
not change the equation nor the wave cone.
-/

@[expose] public section

open MeasureTheory Matrix PDE

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The coefficients with the indices `|α| > k` replaced by `0`. -/
def truncCoeff (k : ℕ) (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ) :
    (Fin d → ℕ) → Vec d → Matrix κ ι ℝ :=
  fun α => if ∑ i, α i ≤ k then A α else fun _ => 0

omit [Fintype ι] [Fintype κ] in
theorem truncCoeff_of_le {k : ℕ} {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ} {α : Fin d → ℕ}
    (h : ∑ i, α i ≤ k) : truncCoeff k A α = A α := by
  simp [truncCoeff, h]

theorem sum_eq_of_mem_antidiagonalTuple {h : ℕ} {α : Fin d → ℕ}
    (hα : α ∈ Finset.Nat.antidiagonalTuple d h) : ∑ i, α i = h :=
  Finset.Nat.mem_antidiagonalTuple.1 hα

omit [Fintype κ] in
theorem isFreeVar_truncCoeff {k : ℕ} {Ω : Set (Vec d)} {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    {μ : VectorMeasure (Vec d) (ι → ℝ)} (h : IsFreeVar Ω k A μ) :
    IsFreeVar Ω k (truncCoeff k A) μ := by
  intro φ hφ j
  refine Eq.trans (Finset.sum_congr rfl fun h' hh' => ?_) (h φ hφ j)
  have hle : h' ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hh')
  refine Finset.sum_congr rfl fun α hα => ?_
  have := truncCoeff_of_le (k := k) (A := A) (by rw [sum_eq_of_mem_antidiagonalTuple hα]; exact hle)
  rw [this]

omit [Fintype κ] in
theorem waveCone_truncCoeff (k : ℕ) (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ) (x : Vec d) :
    waveCone k (fun α => truncCoeff k A α x) = waveCone k (fun α => A α x) := by
  ext P
  refine exists_congr fun ξ => and_congr_right fun _ => ?_
  have : ∀ α ∈ Finset.Nat.antidiagonalTuple d k, truncCoeff k A α x = A α x := fun α hα => by
    rw [truncCoeff_of_le (by rw [sum_eq_of_mem_antidiagonalTuple hα])]
  have hs : ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • truncCoeff k A α x =
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • A α x :=
    Finset.sum_congr rfl fun α hα => by rw [this α hα]
  beta_reduce
  rw [hs]

/-- [DPR, Remark 1.4]: variable coefficients, `C^∞` on `Ω` for `|α| ≤ k`. -/
theorem thm_var {k : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ)
    (hA : ∀ α : Fin d → ℕ, ∑ i, α i ≤ k → ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x i j) Ω)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFreeVar Ω k A μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume,
      polar μ x ∈ waveCone k (fun α => A α x) := by
  have hA' : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => truncCoeff k A α x j i) Ω := by
    intro α j i
    by_cases hα : ∑ i, α i ≤ k
    · rw [truncCoeff_of_le hα]
      exact hA α hα j i
    · have : truncCoeff k A α = fun _ => 0 := by simp [truncCoeff, hα]
      rw [this]
      exact contDiffOn_const
  obtain ⟨hfin, hm, hi, hb, -⟩ := lem_varpair (κ := κ) hΩ k μ
  have hpair := hb (truncCoeff k A) hA' hμ (isFreeVar_truncCoeff hfree)
  have key := thm_main_pair hΩ hA' (euclideanVariation μ) hm hi hpair
  filter_upwards [key] with x hx
  rwa [waveCone_truncCoeff] at hx

end

end AFree
