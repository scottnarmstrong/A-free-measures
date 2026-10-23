module

public import AFree.Paper.OrderK.AlgebraTest

/-!
# From free measures to free pairs

A measure satisfying `IsFreeVar`
(or `IsFree`) gives the `A`-free pair `(|μ|, dμ/d|μ|)`.
-/

@[expose] public section

open MeasureTheory PDE Matrix

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem multiCoordDeriv_const_mul {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ)
    (α : Fin d → ℕ) :
    multiCoordDeriv α (fun y => c * f y) = fun y => c * multiCoordDeriv α f y := by
  have hfs : SmOn Set.univ f := smOn_univ_iff.2 hf
  have key : ∀ l : List (Fin d),
      foldDeriv l α (fun y => c * f y) = fun y => c * foldDeriv l α f y := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      funext x
      show (euclideanCoordDeriv i)^[α i] (foldDeriv l α (fun y => c * f y)) x = _
      rw [ih]
      exact (iterD_const_mul isOpen_univ c (hfs.foldr α l) i (α i)) (Set.mem_univ x)
  exact key _

theorem integral_multiCoordDeriv_mul_polar {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {ψ : Vec d → ℝ}
    (hψ : IsTestFunctionOn Ω ψ) {B : Vec d → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B Ω)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (α : Fin d → ℕ) (i : ι) :
    (∫ᵛ x, multiCoordDeriv α (fun y => ψ y * B y) x ∂•μ) i =
      ∫ x, multiCoordDeriv α (fun y => ψ y * B y) x * polar μ x i ∂euclideanVariation μ := by
  obtain ⟨_, _, _, h⟩ := lem_smoothext hΩ hψ hB
  obtain ⟨hs, _, _, hc, C, hC⟩ := h α
  exact integral_smul_vectorMeasure_apply μ hc.measurable hC i

omit [Fintype κ] in
/-- `σ = |μ|` is finite, `P = dμ/d|μ|` is Borel and in `L¹(σ)`;
(a) `IsFreeVar` with `|μ|(Ωᶜ) = 0` gives an `A`-free pair, and (b) `IsFree` (constant
coefficients) gives an `A`-free pair with constant coefficients. -/
theorem lem_varpair {Ω : Set (Vec d)} (hΩ : IsOpen Ω) (k : ℕ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) :
    IsFiniteMeasure (euclideanVariation μ) ∧ Measurable (polar μ) ∧
      Integrable (polar μ) (euclideanVariation μ) ∧
      (∀ A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ,
        (∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω) →
        euclideanVariation μ Ωᶜ = 0 → IsFreeVar Ω k A μ →
        IsFreePairVar Ω k A (euclideanVariation μ) (polar μ)) ∧
      (∀ A : (Fin d → ℕ) → Matrix κ ι ℝ, euclideanVariation μ Ωᶜ = 0 → IsFree Ω k A μ →
        IsFreeVar Ω k (fun α _ => A α) μ ∧
        IsFreePairVar Ω k (fun α _ => A α) (euclideanVariation μ) (polar μ)) := by
  have ha : ∀ A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ,
      (∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω) →
      euclideanVariation μ Ωᶜ = 0 → IsFreeVar Ω k A μ →
      IsFreePairVar Ω k A (euclideanVariation μ) (polar μ) := by
    intro A hA hμ hfree
    refine ⟨hμ, fun ψ hψ j => ?_⟩
    have h := hfree ψ hψ j
    rw [← h]
    refine Finset.sum_congr rfl fun h' _ => Finset.sum_congr rfl fun α _ => ?_
    congr 1
    have hint : ∀ i, Integrable (fun x => multiCoordDeriv α (fun z => ψ z * A α z j i) x *
        polar μ x i) (euclideanVariation μ) := by
      intro i
      obtain ⟨_, _, _, hh⟩ := lem_smoothext hΩ hψ (hA α j i)
      obtain ⟨_, _, _, hc, C, hC⟩ := hh α
      exact (integrable_polar_apply μ i).bdd_mul hc.measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall hC)
    rw [integral_finsetSum _ fun i _ => hint i]
    exact Finset.sum_congr rfl fun i _ =>
      (integral_multiCoordDeriv_mul_polar hΩ hψ (hA α j i) μ α i).symm
  refine ⟨inferInstance, measurable_polar μ, integrable_polar μ, ha, fun A hμ hfree => ?_⟩
  have hv : IsFreeVar Ω k (fun α _ => A α) μ := by
    intro φ hφ j
    have h := congrFun (hfree φ hφ) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    refine Eq.trans (Finset.sum_congr rfl fun h' _ => Finset.sum_congr rfl fun α _ => ?_) h
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := integral_multiCoordDeriv_mul_polar hΩ hφ (contDiffOn_const (c := A α j i)) μ α i
    have hcc := isCc_multiCoordDeriv (⟨hφ.1, hφ.2.1⟩ : IsCc φ) α
    obtain ⟨C, hC⟩ := hcc.1.continuous.bounded_above_of_compact_support hcc.2
    have e2 := integral_smul_vectorMeasure_apply μ hcc.1.continuous.measurable hC i
    rw [e1, e2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : multiCoordDeriv α (fun y => φ y * A α j i) = fun y => A α j i * multiCoordDeriv α φ y := by
      rw [← multiCoordDeriv_const_mul hφ.1]
      simp only [mul_comm]
    simp only [this]
    ring
  exact ⟨hv, ha _ (fun α j i => contDiffOn_const) hμ hv⟩

end

end AFree
