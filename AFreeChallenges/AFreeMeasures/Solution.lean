module

public import AFree.Defs
public import AFree.Proofs.WaveConeBridgeProof
public import Mathlib.Analysis.Complex.Basic
public import AFree.Proofs.FirstOrderMainProof
public import AFree.Proofs.GeneralMainProof
public import AFree.Proofs.WaveConeBridgeKProof
public import AFree.Proofs.MeasureRhsProof
public import AFree.Proofs.VariableCoeffProof
public import AFree.Proofs.AlbertiProof
public import AFree.Proofs.TensorPowProof
public import AFree.Proofs.BDProof
public import AFree.Proofs.BDOrthProof
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import AFree.Proofs.HyperplaneProof
public import AFree.Proofs.CovectorKernelProof
public import AFree.Proofs.InteriorProductKernelProof
public import AFree.Proofs.SimpleLinAlgProof
public import AFree.Proofs.SimpleAEProof
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import AFree.Proofs.SimpleCounterexampleProof
public import AFree.Proofs.SpanAbsContProof
public import Mathlib.LinearAlgebra.Matrix.Rank
public import AFree.Proofs.DivRankProof
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import AFree.Proofs.BesselCompactProof
public import AFree.Proofs.RademacherConverseProof
public import AFree.Proofs.DecompBundleExistsProof
public import AFree.Proofs.DecompBundleIffProof
public import AFree.Proofs.AKMassExistsProof
public import AFree.Proofs.MetricCurrentACProof
public import AFree.Proofs.FlatChainProof

/-!
# Solution: the structure of 𝒜-free measures

The 25 statements of `Challenge.lean`, each proved by the corresponding theorem of the library.
-/

@[expose] public section

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- The wave cone `waveConeFirstOrder A` is the paper's `Λ_𝒜 = ⋃_{|ξ|=1} ker 𝔸¹(ξ)`, with the
symbol `𝔸¹(ξ) = 2πi Σ_ℓ ξ_ℓ A_ℓ` ([DPR, Section 2.1]). -/
theorem mem_waveConeFirstOrder_iff_complexSymbol {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Fin d → Matrix κ ι ℝ) (P : ι → ℝ) :
    P ∈ waveConeFirstOrder A ↔
      ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧
        ((2 * Real.pi * Complex.I) • ∑ ℓ, (ξ ℓ : ℂ) • (A ℓ).map (fun a => (a : ℂ))) *ᵥ
          (fun i => (P i : ℂ)) = 0 := by exact AFree.WaveConeBridgeProof.result A P
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Theorem 1.1] for operators of order at most one: if `Σ_ℓ A_ℓ ∂_ℓ μ + A₀ μ = 0` on an
open set `Ω`, then the polar of `μ` lies in the wave cone `Λ_𝒜` at `|μ|ˢ`-almost every point. -/
theorem polar_mem_waveConeFirstOrder {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : Fin d → Matrix κ ι ℝ) (A₀ : Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFirstOrderFree Ω A A₀ μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveConeFirstOrder A := by exact AFree.FirstOrderMainProof.result Ω hΩ A A₀ μ hμ hfree
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [DPR, Theorem 1.1]: if `𝒜μ = Σ_{|α| ≤ k} A_α ∂^α μ = 0` on an open set `Ω`, then the polar of `μ`
lies in the wave cone `Λ_𝒜` at `|μ|ˢ`-almost every point. -/
theorem polar_mem_waveCone {d k : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFree Ω k A μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveCone k A := by exact AFree.GeneralMainProof.result Ω hΩ A μ hμ hfree
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The wave cone `waveCone k A` is the paper's `Λ_𝒜 = ⋃_{|ξ|=1} ker 𝔸^k(ξ)`, with the principal
symbol `𝔸^k(ξ) = (2πi)^k Σ_{|α|=k} ξ^α A_α` ([DPR, Section 2.1]). -/
theorem mem_waveCone_iff_complexSymbol {d k : ℕ} (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P : ι → ℝ) :
    P ∈ waveCone k A ↔ ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧
      ((2 * Real.pi * Complex.I) ^ k •
          ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
            ((∏ i, ξ i ^ α i : ℝ) : ℂ) • (A α).map (fun a => (a : ℂ))) *ᵥ
        (fun i => (P i : ℂ)) = 0 := by exact AFree.WaveConeBridgeKProof.result A P
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [DPR, Remark 1.3]: the conclusion of Theorem 1.1 holds when `𝒜μ = σ` is a measure, for an
operator of order `k ≥ 1`. -/
theorem polar_mem_waveCone_of_eq_measure {d k : ℕ} (hk : 1 ≤ k) (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (σ : VectorMeasure (Vec d) (κ → ℝ)) (hσ : euclideanVariation σ Ωᶜ = 0)
    (hrhs : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
      ∑ h ∈ Finset.range (k + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        (-1 : ℝ) ^ h • (A α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•μ) = ∫ᵛ x, φ x ∂•σ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveCone k A := by exact AFree.MeasureRhsProof.result hk Ω hΩ A μ hμ σ hσ hrhs
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [DPR, Remark 1.4]: Theorem 1.1 for operators with smooth variable coefficients `A_α(x)`,
`|α| ≤ k`, with, at `x`, the wave cone of the operator `Σ_{|α| ≤ k} A_α(x) ∂^α` with coefficients fixed at `x`. -/
theorem polar_mem_waveCone_var {d k : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ)
    (hA : ∀ α : Fin d → ℕ, ∑ i, α i ≤ k → ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x i j) Ω)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (hfree : IsFreeVar Ω k A μ) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume,
      polar μ x ∈ waveCone k (fun α => A α x) := by exact AFree.VariableCoeffProof.result Ω hΩ A hA μ hμ hfree
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Theorem 1.5] (Alberti's rank-one theorem): for `u ∈ BV(Ω; ℝ^ℓ)`, at `|Dˢu|`-almost
every point the polar of `Dˢu` is `a ⊗ b` with `a ≠ 0` and `b ≠ 0`. -/
theorem polar_lebesgueSingularPart_eq_tensor {d ℓ : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω) (u : Vec d → Vec ℓ)
    (Du : VectorMeasure (Vec d) (Fin ℓ × Fin d → ℝ)) (hDu : IsBVGradientOn Ω u Du) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Du),
      ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Du) x = fun p => a p.1 * b p.2 := by exact AFree.AlbertiProof.result Ω hΩ u Du hDu
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Theorem 1.6]: if the `r`-th derivative `Dʳu` of `u ∈ L¹(Ω; ℝ^ℓ)` is a measure, then at
`|Dʳu|ˢ`-almost every point its polar is `a ⊗ b^{⊗r}` with `a ≠ 0` and `b ≠ 0`. -/
theorem polar_lebesgueSingularPart_eq_tensorPow {d ℓ r : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω) (u : Vec d → Vec ℓ)
    (Dr : VectorMeasure (Vec d) (Fin ℓ × (Fin r → Fin d) → ℝ)) (hDr : IsDerivMeasureOn Ω u r Dr) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Dr),
      ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Dr) x = fun p => a p.1 * ∏ m, b (p.2 m) := by exact AFree.TensorPowProof.result Ω hΩ u Dr hDr
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Theorem 1.7]: for `u ∈ BD(Ω)`, at `|Eˢu|`-almost every point the polar of `Eˢu` is
`a ⊙ b = (a ⊗ b + b ⊗ a)/2` with `a ≠ 0` and `b ≠ 0`. -/
theorem polar_lebesgueSingularPart_eq_symmTensor {d : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (u : Vec d → Vec d) (Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ))
    (hEu : IsBDGradientOn Ω u Eu) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      ∃ a : Vec d, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Eu) x = fun p => (a p.1 * b p.2 + b p.1 * a p.2) / 2 := by exact AFree.BDProof.result Ω hΩ u Eu hEu
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Corollary 1.8]: if moreover `div u ∈ L²(Ω)`, the vectors `a` and `b` can be taken with
`a · b = 0`. -/
theorem polar_lebesgueSingularPart_eq_symmTensor_orth {d : ℕ} (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (u : Vec d → Vec d) (Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ))
    (hEu : IsBDGradientOn Ω u Eu)
    (hdiv : ∃ g : Vec d → ℝ, MemLp g 2 (volume.restrict Ω) ∧
      ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
        ∫ x in Ω, ∑ i, u x i * euclideanCoordDeriv i φ x = -∫ x in Ω, g x * φ x) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Eu),
      ∃ a : Vec d, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧ vecDot a b = 0 ∧
        polar (lebesgueSingularPart Eu) x = fun p => (a p.1 * b p.2 + b p.1 * a p.2) / 2 := by exact AFree.BDOrthProof.result Ω hΩ u Eu hEu hdiv
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Corollary 1.9]: for normal `(d-1)`-currents `T₁, …, T_r` on `ℝ^d` without boundary and a
locally finite measure `μ ≪ ‖Tᵢ‖`, at `μˢ`-almost every point there is a hyperplane `V` with
`T⃗ᵢ(x) ∈ Λ_{d-1}(V)` for all `i`. -/
theorem exists_hyperplane_of_boundaryless {d r : ℕ}
    (T : Fin r → VectorMeasure (Vec d) (KVec d (d - 1)))
    (hT : ∀ i, IsBoundaryOn Set.univ (T i) 0)
    (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ i, μ ≪ euclideanVariation (T i)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ V : Submodule ℝ (Vec d), Module.finrank ℝ V = d - 1 ∧
      ∀ i, polar (T i) x ∈ kvecSpan V (d - 1) := by exact AFree.HyperplaneProof.result T hT μ hμ
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Theorem 1.10]: for normal currents `T₁, …, T_r` on `Ω` of dimensions `1 ≤ kᵢ ≤ d` and a
measure `μ` on `Ω`, finite on compact subsets, with `μ ≪ ‖Tᵢ‖`, at `μˢ`-almost every point there is a
covector `ω ≠ 0` with `T⃗ᵢ(x) ⌟ ω = 0` for all `i`. -/
theorem exists_covector_interiorProduct_eq_zero {d r : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω) (k : Fin r → ℕ) (hk : ∀ i, 1 ≤ k i ∧ k i ≤ d)
    (T : (i : Fin r) → VectorMeasure (Vec d) (KVec d (k i))) (hT : ∀ i, IsNormalCurrentOn Ω (T i))
    (μ : Measure (Vec d)) (hμΩ : μ Ωᶜ = 0) (hμloc : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤)
    (hμ : ∀ i, μ ≪ euclideanVariation (T i)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ ω : Vec d, ω ≠ 0 ∧
      ∀ i, interiorProduct (polar (T i) x) ω = 0 := by exact AFree.CovectorKernelProof.result Ω hΩ k hk T hT μ hμΩ hμloc hμ
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Theorem 1.10], the equivalent form of the conclusion: for `k ≥ 1` and `ω ≠ 0`,
`v ⌟ ω = 0` if and only if `v ∈ Λ_k(ker ω)`. -/
theorem interiorProduct_eq_zero_iff_mem_kvecSpan {d k : ℕ} (hk : 1 ≤ k) (ω : Vec d) (hω : ω ≠ 0)
    (v : KVec d k) :
    interiorProduct v ω = 0 ↔ v ∈ kvecSpan (covectorKernel ω) k := by exact AFree.InteriorProductKernelProof.result hk ω hω v
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Remark 1.11], linear algebra: if `dim V = d - 1`, every `w ∈ Λ_{d-2}(V)` is simple. -/
theorem isSimpleKVec_of_mem_kvecSpan {d : ℕ} (V : Submodule ℝ (Vec d))
    (hV : Module.finrank ℝ V = d - 1) (w : KVec d (d - 2)) (hw : w ∈ kvecSpan V (d - 2)) :
    IsSimpleKVec w := by exact AFree.SimpleLinAlgProof.result V hV w hw
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Remark 1.11]: for a locally normal `(d-2)`-current `T = T⃗ ‖T‖` on `ℝ^d`, the polar
`T⃗(x)` is simple for `‖T‖ˢ`-almost every `x`. -/
theorem ae_isSimpleKVec_of_isLocNormalCurrent {d : ℕ} (τ : Measure (Vec d))
    (P : Vec d → KVec d (d - 2)) (hT : IsLocNormalCurrent τ P) :
    ∀ᵐ x ∂τ.singularPart volume, IsSimpleKVec (P x) := by exact AFree.SimpleAEProof.result τ P hT
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Remark 1.11], the example in `ℝ⁵`: `T⃗ = (e₁ ∧ e₂ + e₃ ∧ e₄)/√2` and
`‖T‖ = √2 𝓗⁴ ⌞ {x₅ = 0}` define a locally normal `2`-current whose polar is not simple
`‖T‖ˢ`-almost everywhere. Here `μH[4]` is Mathlib's Hausdorff measure for the sup metric of `Vec 5`;
on the hyperplane `{x₅ = 0}` it equals `𝓛⁴`, that is, the Euclidean `𝓗⁴`. -/
theorem not_ae_isSimpleKVec_example :
    ∃ P : Vec 5 → KVec 5 2,
      (∀ x, P x = fun I => if I.1 = {0, 1} ∨ I.1 = {2, 3} then (Real.sqrt 2)⁻¹ else 0) ∧
      IsLocNormalCurrent
        (ENNReal.ofReal (Real.sqrt 2) • (μH[4] : Measure (Vec 5)).restrict {x | x 4 = 0}) P ∧
      ¬ ∀ᵐ x ∂(ENNReal.ofReal (Real.sqrt 2) •
          (μH[4] : Measure (Vec 5)).restrict {x | x 4 = 0}).singularPart volume,
        IsSimpleKVec (P x) := by exact AFree.SimpleCounterexampleProof.result
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Corollary 1.12]: if `μ ≪ ‖Tᵢ‖` for normal `1`-currents `T₁, …, T_d` on `ℝ^d` whose
polars span `ℝ^d` at `μ`-almost every point, then `μ ≪ 𝓛^d`. -/
theorem absolutelyContinuous_of_span_eq_top {d : ℕ}
    (T : Fin d → VectorMeasure (Vec d) (KVec d 1)) (hT : ∀ i, IsNormalCurrentOn Set.univ (T i))
    (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ i, μ ≪ euclideanVariation (T i))
    (hspan : ∀ᵐ x ∂μ, Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)) = ⊤) :
    μ ≪ volume := by exact AFree.SpanAbsContProof.result T hT μ hμ hspan
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Corollary 1.13]: if `μ ∈ ℳ(Ω; ℝ^{d×d})` and `Div μ ∈ ℳ(Ω; ℝ^d)`, then the polar of `μ` has
rank at most `d - 1` at `|μ|ˢ`-almost every point. -/
theorem rank_polar_le_of_div_eq {d : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (μ : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)) (hμ : euclideanVariation μ Ωᶜ = 0)
    (σ : VectorMeasure (Vec d) (Vec d)) (hσ : euclideanVariation σ Ωᶜ = 0)
    (hdiv : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∀ k,
      -∑ j, (∫ᵛ x, euclideanCoordDeriv j φ x ∂•μ) (k, j) = (∫ᵛ x, φ x ∂•σ) k) :
    ∀ᵐ x ∂(euclideanVariation μ).singularPart volume,
      (Matrix.of fun k j => polar μ x (k, j)).rank ≤ d - 1 := by exact AFree.DivRankProof.result Ω hΩ μ hμ σ hσ hdiv
end AFree
end

section
open MeasureTheory Matrix
namespace AFree
open PDE

/-- [DPR, Lemma 2.1]: for `s > 0` and `1 ≤ p < p(d, s)`, the Bessel potential `(Id - Δ)^{-s/2}`,
applied to smooth functions supported in the unit ball, extends to a compact operator `L¹_c(B₁) → L^p`. -/
theorem exists_compact_besselPotential {d : ℕ} {s : ℝ} (hs : 0 < s) {p : ENNReal}
    [Fact (1 ≤ p)] (hp : p < besselExponent d s) :
    ∃ T : L1Ball d →L[ℝ] Lp ℝ p (volume : Measure (Vec d)), IsCompactOperator T ∧
      ∀ u : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → tsupport u ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ f : L1Ball d, ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume] u →
          ((T f : Lp ℝ p (volume : Measure (Vec d))) : Vec d → ℝ) =ᵐ[volume]
            fun x => (besselPotential s u x).re := by exact AFree.BesselCompactProof.result hs hp
end AFree
end

section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval
namespace AFree
open PDE

/-- [DPR, Theorem 1.14] (converse of Rademacher's theorem): if every Lipschitz function on `ℝ^d`
is differentiable `μ`-almost everywhere, then `μ ≪ 𝓛^d`. -/
theorem absolutelyContinuous_of_ae_differentiableAt {d : ℕ} (μ : Measure (Vec d))
    [IsLocallyFiniteMeasure μ]
    (hμ : ∀ f : Vec d → ℝ, (∃ K, LipschitzWith K f) → ∀ᵐ x ∂μ, DifferentiableAt ℝ f x) :
    μ ≪ volume := by exact AFree.RademacherConverseProof.result μ hμ
end AFree
end

section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval
namespace AFree
open PDE

/-- Every finite measure has a decomposability bundle `V(μ, ·)` ([AM, Section 2.7 and
Lemma 2.3]). -/
theorem exists_isDecompBundle {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    ∃ V, IsDecompBundle μ V := by exact AFree.DecompBundleExistsProof.result μ
end AFree
end

section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval
namespace AFree
open PDE

/-- [DPR, Lemma 3.1]: `V(μ, x) = ℝ^d` for `μ`-almost every `x` if and only if there are normal
`1`-currents `T₁, …, T_d` with `μ ≪ ‖Tᵢ‖` whose polars span `ℝ^d` at `μ`-almost every point. -/
theorem decompBundle_eq_top_iff {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    (∃ V, IsDecompBundle μ V ∧ ∀ᵐ x ∂μ, V x = ⊤) ↔
      ∃ T : Fin d → VectorMeasure (Vec d) (KVec d 1), (∀ i, IsNormalCurrentOn Set.univ (T i)) ∧
        (∀ i, μ ≪ euclideanVariation (T i)) ∧
        ∀ᵐ x ∂μ, Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)) = ⊤ := by exact AFree.DecompBundleIffProof.result μ
end AFree
end

section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval
namespace AFree
open PDE

/-- [AK, Definition 2.6]: a metric functional with finite mass has a mass `‖T‖`, the least finite
measure satisfying [AK, (2.2)]. -/
theorem exists_isAKMass {d k : ℕ} (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ)
    (hT : IsMetricFunctional k T) (hfin : ∃ μ, IsAKMassAdmissible T μ) :
    ∃ μ, IsAKMass T μ := by exact AFree.AKMassExistsProof.result T hT hfin
end AFree
end

section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval
namespace AFree
open PDE

/-- [DPR, Theorem 1.15]: the mass `‖T‖` of every metric `d`-current `T` in `ℝ^d` is absolutely
continuous with respect to `𝓛^d`. -/
theorem absolutelyContinuous_of_isAKMass {d : ℕ} (T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ)
    (hT : IsMetricCurrent d T) (μ : Measure (Vec d)) (hμ : IsAKMass T μ) : μ ≪ volume := by exact AFree.MetricCurrentACProof.result T hT μ hμ
end AFree
end

section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval
namespace AFree
open PDE

/-- [DPR, Theorem 1.15], identification of metric `d`-currents with flat `d`-chains, for compactly
supported currents as in [AK, Theorem 11.1]. A compactly supported metric current `T` and a flat chain
`S` correspond when `∫ f dS = T(f, x₁, …, x_d)` for smooth compactly supported `f`. Every such `T`
has a corresponding flat chain, every flat chain corresponds to such a `T`, and `T` is determined by
these values. -/
theorem isTopFlatChain_iff_isMetricCurrent {d : ℕ} :
    (∀ T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ, IsMetricCurrent d T → HasCompactAKSupport T →
      ∃ S, IsTopFlatChain S ∧ ∀ f, IsTestFunctionOn Set.univ f →
        (∫ᵛ x, f x ∂•S) (topKIdx d) = T f (fun i x => x i)) ∧
    (∀ S, IsTopFlatChain S → ∃ T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ,
      IsMetricCurrent d T ∧ HasCompactAKSupport T ∧ ∀ f, IsTestFunctionOn Set.univ f →
        (∫ᵛ x, f x ∂•S) (topKIdx d) = T f (fun i x => x i)) ∧
    (∀ T₁ T₂ : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ, IsMetricCurrent d T₁ →
      HasCompactAKSupport T₁ → IsMetricCurrent d T₂ → HasCompactAKSupport T₂ →
      (∀ f, IsTestFunctionOn Set.univ f → T₁ f (fun i x => x i) = T₂ f (fun i x => x i)) →
      ∀ f, IsBddLipFun f → ∀ π : Fin d → Vec d → ℝ, (∀ i, IsLipFun (π i)) → T₁ f π = T₂ f π) := by exact AFree.FlatChainProof.result
end AFree
end
