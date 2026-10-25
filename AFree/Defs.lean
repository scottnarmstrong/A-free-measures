module

public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Sobolev.ClassicalLaplacian
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Definitions

The definitions used in the statements of the main theorems, in four parts:

1. measures, polars and first-order operators ([DPR, Section 2.1]);
2. higher derivatives, `k`-vectors and normal currents ([DPR, Theorem 1.6, Corollary 1.9,
   Theorem 1.10, Remark 1.11 and Corollary 1.12]);
3. operators of order `k`, BD functions and Bessel potentials ([DPR, Theorem 1.1, Remarks 1.3 and
   1.4, Theorem 1.7, Corollary 1.8 and Lemma 2.1]);
4. metric currents, flat chains and the decomposability bundle ([DPR, Theorems 1.14 and 1.15 and
   Lemma 3.1], after [AK] and [AM]).

`ℝ^d` is `Vec d = Fin d → ℝ` with Lebesgue measure. A vector measure takes values in `ι → ℝ` for a
finite index type `ι`; a measure on `Ω` is one whose total variation vanishes outside `Ω`. Total
variations, polars, `k`-vectors, Lipschitz constants, diameters and `𝓗¹` are taken for the
Euclidean norm.

All definitions are in one module, so that `AFreeChallenges/AFreeMeasures/Challenge.lean`, which
restates them in one file, elaborates to the same constants.
-/

@[expose] public section

/-! ## Measures, polars and first-order operators

* `piEuclideanNorm`: the Euclidean norm on `ι → ℝ`.
* `euclideanVariation μ`: the total variation `|μ|`.
* `coordMeasure μ i`: the coordinate `μᵢ` as a signed measure.
* `polar μ`: the polar `dμ/d|μ|`.
* `lebesgueSingularPart μ`: the singular part `μˢ` with respect to Lebesgue measure.
* `IsTestFunctionOn Ω φ`: `φ ∈ C_c^∞(Ω)`.
* `IsFirstOrderFree Ω A A₀ μ`: `Σ_ℓ A_ℓ ∂_ℓ μ + A₀ μ = 0` in `𝒟'(Ω)`.
* `waveConeFirstOrder A`: the wave cone `Λ_𝒜` of a first-order operator.
* `IsBVGradientOn Ω u Du`: `Du` is the distributional gradient of `u ∈ BV(Ω; ℝ^ℓ)`.
-/

section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Euclidean norm `|v| = (Σᵢ vᵢ²)^{1/2}` on the coordinate space `ι → ℝ`. -/
noncomputable def piEuclideanNorm (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i * v i)

/-- σ-subadditivity of `s ↦ |μ(s)|` (Euclidean norm), needed to build the total variation. -/
theorem isSigmaSubadditiveSetFun_piEuclideanNorm {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (ι → ℝ)) :
    IsSigmaSubadditiveSetFun (fun s => ENNReal.ofReal (piEuclideanNorm (μ s))) := by
  let e : (ι → ℝ) →+ PiLp 2 (fun _ : ι => ℝ) :=
    { toFun := WithLp.toLp 2, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have he : Continuous e := PiLp.continuous_toLp 2 _
  have key : (fun s => ENNReal.ofReal (piEuclideanNorm (μ s))) =
      fun s => ‖(μ.mapRange e he) s‖ₑ := by
    funext s
    rw [VectorMeasure.mapRange_apply, ← ofReal_norm, PiLp.norm_eq_of_L2]
    simp only [piEuclideanNorm, Real.norm_eq_abs, sq, abs_mul_abs_self]
    rfl
  rw [key]
  exact VectorMeasure.isSigmaSubadditiveSetFun_enorm _

/-- The total variation `|μ|` of an `ℝ^ι`-valued measure with respect to the Euclidean norm:
`|μ|(E) = sup Σₖ |μ(Eₖ)|` over finite measurable partitions of `E` (Mathlib's `preVariation`;
for a countably additive `μ` this equals the supremum over countable partitions). -/
noncomputable def euclideanVariation {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (ι → ℝ)) : Measure X :=
  preVariation (fun s => ENNReal.ofReal (piEuclideanNorm (μ s)))
    (isSigmaSubadditiveSetFun_piEuclideanNorm μ)
    ((congrArg (fun v : ι → ℝ => ENNReal.ofReal (piEuclideanNorm v)) μ.empty).trans
      ((congrArg ENNReal.ofReal
          ((congrArg Real.sqrt (Finset.sum_eq_zero fun i _ => mul_zero ((0 : ι → ℝ) i))).trans
            Real.sqrt_zero)).trans ENNReal.ofReal_zero))

/-- The `i`-th coordinate `μᵢ` of an `ℝ^ι`-valued measure, as a signed measure. -/
noncomputable def coordMeasure {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (ι → ℝ)) (i : ι) : SignedMeasure X :=
  μ.mapRange (Pi.evalAddMonoidHom (fun _ : ι => ℝ) i) (continuous_apply i)

/-- The polar `dμ/d|μ|`: coordinatewise Radon–Nikodym derivative of `μ` with respect to its
Euclidean total variation. -/
noncomputable def polar {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (ι → ℝ)) (x : X) : ι → ℝ :=
  fun i => (coordMeasure μ i).rnDeriv (euclideanVariation μ) x

/-- The singular part `μˢ` of an `ℝ^ι`-valued measure on `Vec d` with respect to Lebesgue
measure (coordinatewise Lebesgue decomposition). -/
noncomputable def lebesgueSingularPart {d : ℕ} (μ : VectorMeasure (Vec d) (ι → ℝ)) :
    VectorMeasure (Vec d) (ι → ℝ) where
  measureOf' s := fun i => (coordMeasure μ i).singularPart volume s
  empty' := funext fun _ => VectorMeasure.empty _
  not_measurable' _ hs := funext fun _ => VectorMeasure.not_measurable _ hs
  m_iUnion' _ hf hdisj := Pi.hasSum.2 fun _ => VectorMeasure.m_iUnion _ hf hdisj

/-- `φ ∈ C_c^∞(Ω)`: smooth, compactly supported, with support in `Ω`. -/
def IsTestFunctionOn {d : ℕ} (Ω : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- `𝒜μ = Σ_ℓ A_ℓ ∂_ℓ μ + A₀ μ = 0` in `𝒟'(Ω; ℝ^κ)`, tested coordinatewise against scalar test
functions, with `⟨∂_ℓ μ, φ⟩ = -∫ ∂_ℓ φ dμ`. -/
def IsFirstOrderFree {d : ℕ} (Ω : Set (Vec d)) (A : Fin d → Matrix κ ι ℝ) (A₀ : Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) : Prop :=
  ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
    A₀ *ᵥ (∫ᵛ x, φ x ∂•μ) = ∑ ℓ, A ℓ *ᵥ (∫ᵛ x, euclideanCoordDeriv ℓ φ x ∂•μ)

/-- The wave cone of a first-order operator: `Λ_𝒜 = ⋃_{|ξ|=1} ker (Σ_ℓ ξ_ℓ A_ℓ)` (real form; the
paper's symbol `2πi Σ_ℓ ξ_ℓ A_ℓ` differs by a nonzero scalar, see the bridge theorem). -/
def waveConeFirstOrder {d : ℕ} (A : Fin d → Matrix κ ι ℝ) : Set (ι → ℝ) :=
  {P | ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧ (∑ ℓ, ξ ℓ • A ℓ) *ᵥ P = 0}

/-- `Du` is the distributional gradient on `Ω` of `u ∈ L¹(Ω; ℝ^ℓ)` and is a finite
`ℝ^{ℓ×d}`-valued measure on `Ω`: `∫_Ω u_k ∂_j φ = -∫ φ dDu_{kj}`. So `u ∈ BV(Ω; ℝ^ℓ)`
iff such a `Du` exists. -/
def IsBVGradientOn {d ℓ : ℕ} (Ω : Set (Vec d)) (u : Vec d → Vec ℓ)
    (Du : VectorMeasure (Vec d) (Fin ℓ × Fin d → ℝ)) : Prop :=
  IntegrableOn u Ω ∧ euclideanVariation Du Ωᶜ = 0 ∧
    ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∀ k j,
      ∫ x in Ω, u x k * euclideanCoordDeriv j φ x = -(∫ᵛ x, φ x ∂•Du) (k, j)

end AFree

end

/-! ## Higher derivatives, `k`-vectors and normal currents

* `iteratedCoordDeriv`, `IsDerivMeasureOn`: `Dʳu` as a measure.
* `KIdx`, `KVec`, `insertSign`, `interiorProduct`, `wedge`, `IsSimpleKVec`, `kvecSpan`,
  `covectorKernel`: `k`-vectors and covectors.
* `IsBoundaryOn`, `IsNormalCurrentOn`, `IsLocNormalCurrent`, `kvecOneToVec`: normal currents.
-/

section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Theorem 1.6]: `∂_{i₁} ⋯ ∂_{i_r} φ` for a multi-index list `i : Fin r → Fin d`. -/
noncomputable def iteratedCoordDeriv {d r : ℕ} (i : Fin r → Fin d) (φ : Vec d → ℝ) : Vec d → ℝ :=
  (List.ofFn i).foldr (fun j g => euclideanCoordDeriv j g) φ

/-- [DPR, Theorem 1.6]: `Dʳu` is the `r`-th distributional derivative on `Ω` of `u ∈ L¹(Ω; ℝ^ℓ)` and is a finite
measure on `Ω` with values in `SLinʳ(ℝ^d; ℝ^ℓ)`, recorded by its values on basis tuples:
`∫_Ω u_k ∂_{i₁}⋯∂_{i_r} φ = (-1)^r ∫ φ d(Dʳu)_{(k,i)}`. (The values are automatically symmetric in `i`.) -/
def IsDerivMeasureOn {d ℓ : ℕ} (Ω : Set (Vec d)) (u : Vec d → Vec ℓ) (r : ℕ)
    (Dr : VectorMeasure (Vec d) (Fin ℓ × (Fin r → Fin d) → ℝ)) : Prop :=
  IntegrableOn u Ω ∧ euclideanVariation Dr Ωᶜ = 0 ∧
    ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∀ (k : Fin ℓ) (i : Fin r → Fin d),
      ∫ x in Ω, u x k * iteratedCoordDeriv i φ x = (-1) ^ r * (∫ᵛ x, φ x ∂•Dr) (k, i)

/-- Index set of the standard basis `e_I = e_{i₁} ∧ ⋯ ∧ e_{i_k}` (`i₁ < ⋯ < i_k`) of `Λ_k(ℝ^d)`. -/
abbrev KIdx (d k : ℕ) := {I : Finset (Fin d) // I.card = k}

/-- `k`-vectors in coordinates (also `k`-covectors, in the dual basis). -/
abbrev KVec (d k : ℕ) := KIdx d k → ℝ

/-- The sign `(-1)^{#{i ∈ J : i < j}}` with `dx^j ∧ dx^J = sign · dx^{J ∪ {j}}` for `j ∉ J`. -/
def insertSign {d : ℕ} (j : Fin d) (J : Finset (Fin d)) : ℝ :=
  (-1) ^ (J.filter (· < j)).card

/-- The interior product `v ⌟ ω ∈ Λ_{k-1}` of `v ∈ Λ_k` and a `1`-covector `ω`, defined by duality:
`⟨v ⌟ ω, ψ⟩ = ⟨v, ω ∧ ψ⟩`. (For `k = 0` it is `0`.) -/
noncomputable def interiorProduct {d k : ℕ} (v : KVec d k) (ω : Vec d) : KVec d (k - 1) :=
  fun J => ∑ j ∈ Finset.univ.filter (· ∉ J.1),
    if h : (insert j J.1).card = k then ω j * insertSign j J.1 * v ⟨insert j J.1, h⟩ else 0

/-- The `k`-vector `v₁ ∧ ⋯ ∧ v_k`: its `I`-coordinate is the `k × k` minor on the rows `I`. -/
noncomputable def wedge {d k : ℕ} (v : Fin k → Vec d) : KVec d k :=
  fun I => Matrix.det (Matrix.of fun a b : Fin k => v b (I.1.orderEmbOfFin I.2 a))

/-- `w` is simple (decomposable): `w = c · v₁ ∧ ⋯ ∧ v_k`. For `k ≥ 1` the scalar can be absorbed into
`v₁`; for `k = 0` every element of `Λ₀ = ℝ` is simple. -/
def IsSimpleKVec {d k : ℕ} (w : KVec d k) : Prop := ∃ (c : ℝ) (v : Fin k → Vec d), w = c • wedge v

/-- `Λ_k(V)`: the span of the `v₁ ∧ ⋯ ∧ v_k` with all `v_i ∈ V`. -/
noncomputable def kvecSpan {d : ℕ} (V : Submodule ℝ (Vec d)) (k : ℕ) : Submodule ℝ (KVec d k) :=
  Submodule.span ℝ {w | ∃ v : Fin k → Vec d, (∀ i, v i ∈ V) ∧ w = wedge v}

/-- `ker ω = {w : ω(w) = 0}` for a `1`-covector `ω` (`ω(w) = w · ω`). -/
def covectorKernel {d : ℕ} (ω : Vec d) : Submodule ℝ (Vec d) where
  carrier := {w | vecDot w ω = 0}
  add_mem' {a b} ha hb :=
    show ∑ i, (a i + b i) * ω i = 0 from
      ((Finset.sum_congr rfl fun i _ => add_mul (a i) (b i) (ω i)).trans Finset.sum_add_distrib).trans
        ((congrArg₂ (· + ·) ha hb).trans (add_zero 0))
  zero_mem' := show ∑ i, (0 : Vec d) i * ω i = 0 from Finset.sum_eq_zero fun i _ => zero_mul (ω i)
  smul_mem' c w hw :=
    show ∑ i, c * w i * ω i = 0 from
      ((Finset.sum_congr rfl fun i _ => mul_assoc c (w i) (ω i)).trans (Finset.mul_sum _ _ _).symm).trans
        ((congrArg (c * ·) hw).trans (mul_zero c))

/-- `S` is the boundary of the `k`-current `T` on `Ω`, both finite measures on `Ω` with values in
`Λ_k`, `Λ_{k-1}`: `⟨∂T, ψ⟩ = ⟨T, dψ⟩` for `ψ ∈ 𝒟^{k-1}(Ω)`, tested on `ψ = φ dx^J`, where
`d(φ dx^J) = Σ_{j ∉ J} insertSign j J · ∂_jφ dx^{J ∪ {j}}`. (For `k = 0` the sum is empty, so `S = 0`:
the boundary of a `0`-current is zero by convention.) -/
def IsBoundaryOn {d k : ℕ} (Ω : Set (Vec d)) (T : VectorMeasure (Vec d) (KVec d k))
    (S : VectorMeasure (Vec d) (KVec d (k - 1))) : Prop :=
  euclideanVariation S Ωᶜ = 0 ∧ ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∀ J : KIdx d (k - 1),
    (∫ᵛ x, φ x ∂•S) J = ∑ j ∈ Finset.univ.filter (· ∉ J.1),
      if h : (insert j J.1).card = k then
        insertSign j J.1 * (∫ᵛ x, euclideanCoordDeriv j φ x ∂•T) ⟨insert j J.1, h⟩ else 0

/-- `T ∈ 𝐍_k(Ω)`: a `k`-current of finite mass on `Ω` whose boundary has finite mass. -/
def IsNormalCurrentOn {d k : ℕ} (Ω : Set (Vec d)) (T : VectorMeasure (Vec d) (KVec d k)) : Prop :=
  euclideanVariation T Ωᶜ = 0 ∧ ∃ S : VectorMeasure (Vec d) (KVec d (k - 1)), IsBoundaryOn Ω T S

/-- A `1`-vector as a vector of `ℝ^d` (`e_{{j}} ↦ e_j`). -/
def kvecOneToVec {d : ℕ} (v : KVec d 1) : Vec d := fun j => v ⟨{j}, Finset.card_singleton j⟩

/-- A locally normal `k`-current on `ℝ^d` in polar form `T = T⃗ ‖T‖`: `‖T‖ = τ` is locally finite,
`T⃗ = P` is Borel with `|P| = 1` `τ`-a.e., and `∂T = P' τ'` with `τ'` locally finite and `P'`
locally `τ'`-integrable. -/
def IsLocNormalCurrent {d k : ℕ} (τ : Measure (Vec d)) (P : Vec d → KVec d k) : Prop :=
  IsLocallyFiniteMeasure τ ∧ Measurable P ∧ (∀ᵐ x ∂τ, piEuclideanNorm (P x) = 1) ∧
    ∃ (τ' : Measure (Vec d)) (P' : Vec d → KVec d (k - 1)), IsLocallyFiniteMeasure τ' ∧
      Measurable P' ∧ LocallyIntegrable P' τ' ∧
      ∀ φ : Vec d → ℝ, IsTestFunctionOn Set.univ φ → ∀ J : KIdx d (k - 1),
        ∫ x, φ x * P' x J ∂τ' = ∑ j ∈ Finset.univ.filter (· ∉ J.1),
          if h : (insert j J.1).card = k then
            insertSign j J.1 * ∫ x, euclideanCoordDeriv j φ x * P x ⟨insert j J.1, h⟩ ∂τ else 0

end AFree

end

/-! ## Operators of order `k`, BD and Bessel potentials

* `multiCoordDeriv`, `IsFree`, `waveCone`: operators of order `k` and their wave cone.
* `IsFreeVar`: variable coefficients.
* `IsBDGradientOn`: the symmetrised gradient of `u ∈ BD(Ω)`.
* `vecFourierTransform`, `besselPotential`, `L1Ball`, `besselExponent`: Bessel potentials.
-/

section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `∂^α φ = ∂₁^{α₁} ⋯ ∂_d^{α_d} φ` for a multi-index `α : Fin d → ℕ`. -/
noncomputable def multiCoordDeriv {d : ℕ} (α : Fin d → ℕ) (φ : Vec d → ℝ) : Vec d → ℝ :=
  (List.finRange d).foldr (fun i g => (euclideanCoordDeriv i)^[α i] g) φ

/-- `𝒜μ = Σ_{|α| ≤ k} A_α ∂^α μ = 0` in `𝒟'(Ω; ℝ^κ)` (constant coefficients), tested coordinatewise:
`⟨A_α ∂^α μ, φ e⟩ = (-1)^{|α|} e · A_α ∫ ∂^α φ dμ`. Only `A α` with `|α| ≤ k` enter. -/
def IsFree {d : ℕ} (Ω : Set (Vec d)) (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) : Prop :=
  ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
    ∑ h ∈ Finset.range (k + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
      (-1 : ℝ) ^ h • (A α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•μ) = 0

/-- The wave cone of an operator of order `k`: `Λ_𝒜 = ⋃_{|ξ|=1} ker Σ_{|α|=k} ξ^α A_α` (real form;
the paper's principal symbol `𝔸^k(ξ) = (2πi)^k Σ_{|α|=k} A_α ξ^α` differs by a nonzero scalar). -/
def waveCone {d : ℕ} (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) : Set (ι → ℝ) :=
  {P | ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧
    (∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • A α) *ᵥ P = 0}

/-- Remark 1.4: `Σ_{|α| ≤ k} A_α(x) ∂^α μ = 0` in `𝒟'(Ω; ℝ^κ)` with variable coefficients, tested
against `φ e_j`: `⟨A_α ∂^α μ, φ e_j⟩ = (-1)^{|α|} ∫ ∂^α(φ · (A_α)_{j·}) · dμ`. -/
def IsFreeVar {d : ℕ} (Ω : Set (Vec d)) (k : ℕ) (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ)
    (μ : VectorMeasure (Vec d) (ι → ℝ)) : Prop :=
  ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∀ j : κ,
    ∑ h ∈ Finset.range (k + 1), ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
      (-1 : ℝ) ^ h * ∑ i : ι, (∫ᵛ x, multiCoordDeriv α (fun y => φ y * A α y j i) x ∂•μ) i = 0

/-- `Eu` is the symmetrised distributional gradient on `Ω` of `u ∈ L¹(Ω; ℝ^d)` and is a finite measure
on `Ω` (values in `ℝ^{d×d}`, automatically symmetric): `∫_Ω (u_i ∂_jφ + u_j ∂_iφ)/2 = -∫ φ dEu_{ij}`.
So `u ∈ BD(Ω)` iff such an `Eu` exists. -/
def IsBDGradientOn {d : ℕ} (Ω : Set (Vec d)) (u : Vec d → Vec d)
    (Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)) : Prop :=
  IntegrableOn u Ω ∧ euclideanVariation Eu Ωᶜ = 0 ∧
    ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∀ i j,
      ∫ x in Ω, (u x i * euclideanCoordDeriv j φ x + u x j * euclideanCoordDeriv i φ x) / 2 =
        -(∫ᵛ x, φ x ∂•Eu) (i, j)

/-- The Fourier transform `û(ξ) = ∫ u(x) e^{-2πi x·ξ} dx` (paper's convention, Euclidean pairing). -/
noncomputable def vecFourierTransform {d : ℕ} (u : Vec d → ℂ) (ξ : Vec d) : ℂ :=
  ∫ x, Complex.exp (-(2 * Real.pi * Complex.I * (vecDot x ξ : ℂ))) * u x

/-- Lemma 2.1: `(Id - Δ)^{-s/2} u = 𝓕⁻¹[(1 + 4π²|ξ|²)^{-s/2} û]`. -/
noncomputable def besselPotential {d : ℕ} (s : ℝ) (u : Vec d → ℝ) (x : Vec d) : ℂ :=
  ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (vecDot x ξ : ℂ)) *
    ((1 + 4 * Real.pi ^ 2 * vecNormSq ξ) ^ (-s / 2) : ℝ) * vecFourierTransform (fun y => (u y : ℂ)) ξ

/-- `L¹_c(B₁)`: integrable functions vanishing a.e. outside `B₁`, as a submodule of `L¹`. -/
def L1Ball (d : ℕ) : Submodule ℝ (Lp ℝ 1 (volume : Measure (Vec d))) where
  carrier := {f | ∀ᵐ x, x ∉ euclideanBall (0 : Vec d) 1 → f x = 0}
  add_mem' {f g} hf hg := by
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hfx hgx hfg hx
    rw [hfg, Pi.add_apply, hfx hx, hgx hx, add_zero]
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℝ 1 (volume : Measure (Vec d))] with x hx _
    rw [hx, Pi.zero_apply]
  smul_mem' c f hf := by
    filter_upwards [hf, Lp.coeFn_smul c f] with x hfx hcf hx
    rw [hcf, Pi.smul_apply, hfx hx, smul_zero]

/-- The exponent `p(d,s) = d/(d-s)` if `s < d`, `∞` otherwise. -/
noncomputable def besselExponent (d : ℕ) (s : ℝ) : ENNReal :=
  if s < d then ENNReal.ofReal (d / (d - s)) else ⊤

end AFree

end

/-! ## Metric currents, flat chains and the decomposability bundle

* Lipschitz classes: `IsEuclLipschitzWith`, `IsLipFun`, `IsBddLipFun`.
* Metric currents: `IsMetricFunctional`, `IsAKMassAdmissible`, `IsAKMass`, `IsMetricCurrent`,
  `HasCompactAKSupport`; top-dimensional flat chains: `topKIdx`, `IsTopFlatChain`.
* The decomposability bundle: `euclideanDiam`, `euclideanHausdorffOne`, `IsOneRectifiable`, `IsC1Arc`,
  `IsBorelSubspaceField`, `IsRectifiableFamily`, `IsDecompTestField`, `IsDecompBundle`.
-/

section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval

namespace AFree

open PDE

/-! ### Lipschitz functions on `ℝ^d` with the Euclidean distance -/

/-- `π` is `K`-Lipschitz for the Euclidean distance on `ℝ^d`. -/
def IsEuclLipschitzWith {d : ℕ} (K : ℝ≥0) (π : Vec d → ℝ) : Prop :=
  ∀ x y, |π x - π y| ≤ K * vecEuclideanNorm (x - y)

/-- `π ∈ Lip(ℝ^d)`. -/
def IsLipFun {d : ℕ} (π : Vec d → ℝ) : Prop := ∃ K : ℝ≥0, IsEuclLipschitzWith K π

/-- `f ∈ Lip_b(ℝ^d)`: bounded and Lipschitz. -/
def IsBddLipFun {d : ℕ} (f : Vec d → ℝ) : Prop := IsLipFun f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C

/-! ### Ambrosio–Kirchheim metric currents in `ℝ^d` ([AK, Sections 2–3], `E = ℝ^d` Euclidean)

A `k`-dimensional metric functional is a function on `Dᵏ(ℝ^d) = Lip_b(ℝ^d) × Lip(ℝ^d)ᵏ`
([AK, Definition 2.1]), here a function `T f π` on all pairs of which only the values on `Dᵏ` are used. -/

/-- [AK, Definition 2.2]: `T` is subadditive and positively `1`-homogeneous in each of `f, π₁, …, π_k`, in
AK's sense: `|T(x + y)| ≤ |T x| + |T y|` and `|T(t x)| = t |T x|` for `t ≥ 0`. -/
def IsMetricFunctional {d : ℕ} (k : ℕ) (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ) : Prop :=
  (∀ f g, IsBddLipFun f → IsBddLipFun g → ∀ π : Fin k → Vec d → ℝ, (∀ i, IsLipFun (π i)) →
      |T (f + g) π| ≤ |T f π| + |T g π|) ∧
  (∀ f, IsBddLipFun f → ∀ π : Fin k → Vec d → ℝ, (∀ i, IsLipFun (π i)) → ∀ t : ℝ, 0 ≤ t →
      |T (t • f) π| = t * |T f π|) ∧
  (∀ f, IsBddLipFun f → ∀ π : Fin k → Vec d → ℝ, (∀ i, IsLipFun (π i)) → ∀ i ψ, IsLipFun ψ →
      |T f (Function.update π i (π i + ψ))| ≤ |T f π| + |T f (Function.update π i ψ)|) ∧
  (∀ f, IsBddLipFun f → ∀ π : Fin k → Vec d → ℝ, (∀ i, IsLipFun (π i)) → ∀ i, ∀ t : ℝ, 0 ≤ t →
      |T f (Function.update π i (t • π i))| = t * |T f π|)

/-- [AK, (2.2)]: the finite measure `μ` controls `T`:
`|T(f, π₁, …, π_k)| ≤ ∏ Lip(πᵢ) ∫ |f| dμ` on `Dᵏ(ℝ^d)` (Lipschitz constants for the Euclidean
distance; stated for every admissible family of constants, which is equivalent). -/
def IsAKMassAdmissible {d k : ℕ} (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ)
    (μ : Measure (Vec d)) : Prop :=
  IsFiniteMeasure μ ∧ ∀ f, IsBddLipFun f → ∀ (π : Fin k → Vec d → ℝ) (K : Fin k → ℝ≥0),
    (∀ i, IsEuclLipschitzWith (K i) (π i)) → |T f π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |f x| ∂μ

/-- [AK, Definition 2.6]: `μ = ‖T‖` is the mass of `T`, the least measure satisfying (2.2). -/
def IsAKMass {d k : ℕ} (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ) (μ : Measure (Vec d)) :
    Prop :=
  IsAKMassAdmissible T μ ∧ ∀ ν, IsAKMassAdmissible T ν → μ ≤ ν

/-- [AK, Definition 3.1]: `T ∈ M_k(ℝ^d)` is a `k`-dimensional metric functional with finite mass which is
(i) multilinear, (ii) continuous under pointwise convergence of the `πᵢ` with bounded Lipschitz
constants, and (iii) local: `T(f, π) = 0` if some `πᵢ` is constant on a neighbourhood of `{f ≠ 0}`. -/
def IsMetricCurrent {d : ℕ} (k : ℕ) (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ) : Prop :=
  IsMetricFunctional k T ∧ (∃ μ, IsAKMassAdmissible T μ) ∧
  (∀ π : Fin k → Vec d → ℝ, (∀ i, IsLipFun (π i)) → ∀ f g, IsBddLipFun f → IsBddLipFun g →
      ∀ a b : ℝ, T (a • f + b • g) π = a * T f π + b * T g π) ∧
  (∀ f, IsBddLipFun f → ∀ π : Fin k → Vec d → ℝ, (∀ i, IsLipFun (π i)) → ∀ i ψ, IsLipFun ψ →
      ∀ a b : ℝ, T f (Function.update π i (a • π i + b • ψ)) =
        a * T f π + b * T f (Function.update π i ψ)) ∧
  (∀ f, IsBddLipFun f → ∀ π : Fin k → Vec d → ℝ, (∀ i, IsLipFun (π i)) →
    ∀ πn : ℕ → Fin k → Vec d → ℝ, (∃ C : ℝ≥0, ∀ n i, IsEuclLipschitzWith C (πn n i)) →
      (∀ i x, Tendsto (fun n => πn n i x) atTop (𝓝 (π i x))) →
      Tendsto (fun n => T f (πn n)) atTop (𝓝 (T f π))) ∧
  (∀ f, IsBddLipFun f → ∀ π : Fin k → Vec d → ℝ, (∀ i, IsLipFun (π i)) → ∀ i,
    (∃ U : Set (Vec d), IsOpen U ∧ {x | f x ≠ 0} ⊆ U ∧ ∃ c : ℝ, ∀ x ∈ U, π i x = c) →
      T f π = 0)

/-- `spt T = spt ‖T‖` is compact ([AK, Sections 2 and 11]). -/
def HasCompactAKSupport {d k : ℕ} (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ) : Prop :=
  ∃ K : Set (Vec d), IsCompact K ∧ ∀ μ, IsAKMass T μ → μ Kᶜ = 0

/-! ### Federer–Fleming flat chains of top dimension ([AK, Section 11]) -/

/-- The index `{1, …, d}` of `dx₁ ∧ ⋯ ∧ dx_d`, the basis of `Λ_d(ℝ^d)`. -/
def topKIdx (d : ℕ) : KIdx d d := ⟨Finset.univ, Finset.card_fin d⟩

/-- `S ∈ F_d(ℝ^d)` ([AK, Section 11]): a Federer–Fleming `d`-current of finite mass,
here a finite `Λ_d(ℝ^d)`-valued measure, with compact support (flat chains are compactly supported
by definition), which is a limit in mass of normal currents with compact support. -/
def IsTopFlatChain {d : ℕ} (S : VectorMeasure (Vec d) (KVec d d)) : Prop :=
  (∃ K : Set (Vec d), IsCompact K ∧ euclideanVariation S Kᶜ = 0) ∧
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : VectorMeasure (Vec d) (KVec d d), IsNormalCurrentOn Set.univ N ∧
    (∃ K : Set (Vec d), IsCompact K ∧ euclideanVariation N Kᶜ = 0) ∧
    euclideanVariation (S - N) Set.univ < ε

/-! ### The decomposability bundle ([AM, Section 2]) -/

/-- The Euclidean diameter of a set. -/
noncomputable def euclideanDiam {d : ℕ} (s : Set (Vec d)) : ℝ≥0∞ :=
  ⨆ x ∈ s, ⨆ y ∈ s, ENNReal.ofReal (vecEuclideanNorm (x - y))

/-- The one-dimensional Hausdorff measure `𝓗¹` of the Euclidean metric on `ℝ^d`. Mathlib's
`μH[1]` on `Vec d` belongs to the sup metric. Here the cost of a covering set is its Euclidean
diameter; the smallness constraint `diam s ≤ r` of `Measure.mkMetric'` uses the sup metric, which is
equivalent (`diam ≤ euclideanDiam ≤ √d · diam`), so the limit `r ↓ 0` is the Euclidean `𝓗¹`. -/
noncomputable def euclideanHausdorffOne (d : ℕ) : Measure (Vec d) :=
  Measure.mkMetric' euclideanDiam

/-- [AM, Section 2.4]: `E` is `1`-rectifiable: `𝓗¹(E) < ∞` and `E` is covered, up to an `𝓗¹`-null set, by
countably many images of Lipschitz maps `ℝ → ℝ^d`. -/
def IsOneRectifiable {d : ℕ} (E : Set (Vec d)) : Prop :=
  euclideanHausdorffOne d E < ⊤ ∧ ∃ γ : ℕ → ℝ → Vec d, (∀ n, ∃ K, LipschitzWith K (γ n)) ∧
    euclideanHausdorffOne d (E \ ⋃ n, Set.range (γ n)) = 0

/-- A one-dimensional surface of class `C¹` ([AM, Section 2.4]), parametrized by an open interval `J`: `γ` is
`C¹`, injective and immersive on `J`. The image of each compact subinterval `K ⊂ J` is an embedded
`C¹` curve with tangent line `ℝ γ'(s)` at `γ s` for `s` in the interior of `K`, so injective
immersions and embedded `C¹` curves give the same tests below. -/
def IsC1Arc {d : ℕ} (γ : ℝ → Vec d) (J : Set ℝ) : Prop :=
  (∃ a b : ℝ, J = Set.Ioo a b) ∧ ContDiffOn ℝ 1 γ J ∧ Set.InjOn γ J ∧ ∀ s ∈ J, deriv γ s ≠ 0

/-- `V : ℝ^d → Gr(ℝ^d)` is Borel ([AM, Section 2.1], `Gr(ℝ^d)` with the metric `d_gr`; the orthogonal
projection `V ↦ P_V` identifies `(Gr(ℝ^d), d_gr)` isometrically with a closed set of matrices with
the operator norm). -/
def IsBorelSubspaceField {d : ℕ} (V : Vec d → Submodule ℝ (Vec d)) : Prop :=
  ∃ P : Vec d → Matrix (Fin d) (Fin d) ℝ, (∀ i j, Measurable fun x => P x i j) ∧
    ∀ x, (P x).transpose = P x ∧ P x * P x = P x ∧ LinearMap.range (Matrix.toLin' (P x)) = V x

/-- [AM, Section 2.7] (a)–(c): `{μ_t = 𝓗¹⌞E_t}_{t ∈ [0,1]} ∈ 𝓕_μ`: each `E_t` is a Borel `1`-rectifiable
set, `t ↦ μ_t(A)` is Borel for Borel `A`, `∫ ‖μ_t‖ dt < ∞`, and `∫ μ_t dt ≪ μ`. -/
def IsRectifiableFamily {d : ℕ} (μ : Measure (Vec d)) (E : I → Set (Vec d)) : Prop :=
  (∀ t, MeasurableSet (E t) ∧ IsOneRectifiable (E t)) ∧
  (∀ A : Set (Vec d), MeasurableSet A → Measurable fun t => euclideanHausdorffOne d (E t ∩ A)) ∧
  (∫⁻ t, euclideanHausdorffOne d (E t) < ⊤) ∧
  ∀ A : Set (Vec d), MeasurableSet A → μ A = 0 → ∫⁻ t, euclideanHausdorffOne d (E t ∩ A) = 0

/-- [AM, Section 2.7]: `V ∈ 𝓖_μ`: `V` is Borel and `Tan(E_t, x) ⊂ V(x)` for `μ_t`-a.e. `x` and a.e. `t`,
for every `{μ_t} ∈ 𝓕_μ`. The approximate tangent line enters through AM's characterization
[AM, (2.1)]: `Tan(E, x) = Tan(S, x)` for `𝓗¹`-a.e. `x ∈ E ∩ S`, for every `C¹` curve `S`. Since a
`1`-rectifiable set is covered, up to an `𝓗¹`-null set, by countably many `C¹` curves, the inclusion
`Tan(E_t, x) ⊂ V(x)` for `μ_t`-a.e. `x` is equivalent to `Tan(S, x) ⊂ V(x)` for `μ_t`-a.e.
`x ∈ S`, for every `C¹` arc `S`. -/
def IsDecompTestField {d : ℕ} (μ : Measure (Vec d)) (V : Vec d → Submodule ℝ (Vec d)) : Prop :=
  IsBorelSubspaceField V ∧ ∀ E : I → Set (Vec d), IsRectifiableFamily μ E →
    ∀ᵐ t, ∀ (γ : ℝ → Vec d) (J : Set ℝ), IsC1Arc γ J →
      ∀ᵐ x ∂(euclideanHausdorffOne d).restrict (E t ∩ γ '' J),
        ∀ s ∈ J, γ s = x → deriv γ s ∈ V x

/-- [AM, Section 2.7]: `V = V(μ, ·)` is a decomposability bundle of `μ`: a minimal element of `𝓖_μ`
(unique `μ`-a.e.). -/
def IsDecompBundle {d : ℕ} (μ : Measure (Vec d)) (V : Vec d → Submodule ℝ (Vec d)) : Prop :=
  IsDecompTestField μ V ∧ ∀ W, IsDecompTestField μ W → ∀ᵐ x ∂μ, V x ≤ W x

end AFree

end
