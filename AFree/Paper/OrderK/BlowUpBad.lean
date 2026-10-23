module

public import AFree.Paper.OrderK.AlgebraCone
public import AFree.Paper.OrderK.AlgebraTest
public import AFree.Paper.GoodPoints

/-!
# The bad set and the good points of order `k`

The bad set `{P ∉ Λ}` and the existence of good points in it.
-/

@[expose] public section

open MeasureTheory Filter Topology Set PDE

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The cube-to-ball constant `t = 1/(4 √d)`. -/
def badT (d : ℕ) : ℝ := 1 / (4 * Real.sqrt d)

/-- The bad set `E = {x ∈ Ω : P(x) ∉ Λ_x}` with `Λ_x = Λ^{(k)}_{A(x)}`. -/
def badSetK (Ω : Set (Vec d)) (k : ℕ) (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ)
    (P : Vec d → ι → ℝ) : Set (Vec d) :=
  {x | x ∈ Ω ∧ P x ∉ waveCone k (fun α => A α x)}

theorem badT_pos (hd : 0 < d) : 0 < badT d := by
  have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  unfold badT; positivity

theorem badT_lt_one (hd : 0 < d) : badT d < 1 := by
  have hs : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact_mod_cast hd
  unfold badT
  rw [div_lt_one (by positivity)]
  linarith

omit [Fintype κ] in
/-- If `σˢ(E) > 0` there is a point `x₀ ∈ E ∩ Ω` with the properties of a good point
for the blow-up ((i), (ii) of [DPR, Section 2.2] as recalled in Section 2.3, with doubling in place of the tangent-measure step) and `t = 1/(4√d)`. -/
theorem lem_goodk (hd : 0 < d) {Ω : Set (Vec d)} (k : ℕ)
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ} (σ : Measure (Vec d)) [IsFiniteMeasure σ]
    {P : Vec d → ι → ℝ} (hPm : Measurable P) (hPi : Integrable P σ) (hΩ : σ Ωᶜ = 0)
    (hpos : 0 < σ.singularPart volume (badSetK Ω k A P)) :
    ∃ x₀ ∈ badSetK Ω k A P, x₀ ∈ Ω ∧
      (∀ r, 0 < r → 0 < σ.singularPart volume (Metric.closedBall x₀ r)) ∧
      Tendsto (fun r => (∫ y in Metric.closedBall x₀ r, piEuclideanNorm (P y - P x₀)
          ∂σ.singularPart volume) / (σ.singularPart volume (Metric.closedBall x₀ r)).toReal)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r => (∫ y in Metric.closedBall x₀ r, piEuclideanNorm (P y)
          ∂volume.withDensity (σ.rnDeriv volume)) /
            (σ.singularPart volume (Metric.closedBall x₀ r)).toReal) (𝓝[>] 0) (𝓝 0) ∧
      ∀ r₀, 0 < r₀ → ∃ r ∈ Set.Ioo 0 r₀,
        ENNReal.ofReal (badT d ^ (d + 1)) * σ.singularPart volume (Metric.closedBall x₀ r) ≤
          σ.singularPart volume (Metric.closedBall x₀ (badT d * r)) :=
  exists_goodPoint σ hPm hPi hΩ (badT_pos hd) (badT_lt_one hd) hpos

end

end AFree
