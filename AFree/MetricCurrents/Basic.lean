module

public import AFree.Defs
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Metric currents in `ℝ^d`: shared vocabulary

Definitions used throughout the development of metric currents in `ℝ^d`:

* `IsBorelBdd`: the bounded Borel functions `B^∞(ℝ^d)`;
* `IsLipTuple`: `π ∈ Lip^k`;
* `evalTuple`, `matAct`, `jacMat`, `jacDet`, `coordTuple`: the tuple map `x ↦ (π_l x)_l`, the linear
  action `(Aπ)_i = ∑_l A_il π_l`, the Jacobian matrix `(∂_j ψ_i)` and its determinant, and the
  coordinate tuple `x = (x_1, …, x_d)`;
* `akMassMeasure`, `akExt`: a chosen mass measure and the canonical extension `T̄` of `T` to
  `B^∞ × Lip^k` (AK (2.3)); `IsAKExtension` collects the properties (E1)–(E4) of such an extension, listed at its definition.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE

/-- `B^∞(ℝ^d)`: bounded Borel functions `ℝ^d → ℝ`. -/
def IsBorelBdd {d : ℕ} (h : Vec d → ℝ) : Prop :=
  Measurable h ∧ ∃ C : ℝ, ∀ x, |h x| ≤ C

/-- `π ∈ Lip^k`: every component is Lipschitz (Euclidean distance). -/
abbrev IsLipTuple {d k : ℕ} (π : Fin k → Vec d → ℝ) : Prop := ∀ i, IsLipFun (π i)

/-- The point `(π_1(x), …, π_k(x)) ∈ ℝ^k`. -/
def evalTuple {d k : ℕ} (π : Fin k → Vec d → ℝ) (x : Vec d) : Vec k := fun l => π l x

/-- The linear action `(Aπ)_i = ∑_l A_il π_l` of a matrix on a tuple of functions. -/
def matAct {d k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (π : Fin k → Vec d → ℝ) :
    Fin k → Vec d → ℝ :=
  fun i x => ∑ l, A i l * π l x

/-- The Jacobian matrix `Dψ(y) = (∂_j ψ_i(y))_{i,j}` of a tuple `ψ : Vec d → ℝ`, `i ∈ Fin m`. -/
noncomputable def jacMat {d m : ℕ} (ψ : Fin m → Vec d → ℝ) (y : Vec d) :
    Matrix (Fin m) (Fin d) ℝ :=
  Matrix.of fun i j => fderiv ℝ (ψ i) y (Pi.single j 1)

/-- `det Dψ(y)` for a self-map tuple `ψ : Fin k → Vec k → ℝ`. -/
noncomputable def jacDet {k : ℕ} (ψ : Fin k → Vec k → ℝ) (y : Vec k) : ℝ :=
  (jacMat ψ y).det

/-- The coordinate tuple `x = (x_1, …, x_d)`, `x_i(y) = y_i`. -/
def coordTuple (d : ℕ) : Fin d → Vec d → ℝ := fun i y => y i

open Classical in
/-- A chosen mass measure of `T` (the junk value `0` if `T` has none). -/
noncomputable def akMassMeasure {d k : ℕ} (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ) :
    Measure (Vec d) :=
  if H : ∃ μ, IsAKMass T μ then H.choose else 0

open Classical in
/-- A chosen sequence in `Lip_b` converging to `h` in `L¹(μ)` (junk `0` if there is none). -/
noncomputable def akApprox {d : ℕ} (μ : Measure (Vec d)) (h : Vec d → ℝ) : ℕ → Vec d → ℝ :=
  if H : ∃ f : ℕ → Vec d → ℝ, (∀ n, IsBddLipFun (f n)) ∧
      Tendsto (fun n => ∫ x, |f n x - h x| ∂μ) atTop (𝓝 0) then H.choose else fun _ => 0

/-- The canonical extension `T̄(h, π) = lim_n T(f_n, π)` of AK (2.3), where `f_n → h` in
`L¹(‖T‖)`; meaningful for `h ∈ B^∞`, `π ∈ Lip^k` and `T ∈ M_k(ℝ^d)` (see [AK, (2.3)]). -/
noncomputable def akExt {d k : ℕ} (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ) (h : Vec d → ℝ)
    (π : Fin k → Vec d → ℝ) : ℝ :=
  limUnder atTop (fun n => T (akApprox (akMassMeasure T) h n) π)

/-- The properties of an extension `Tb` of `T` to `B^∞ × Lip^k` as in [AK, (2.3)]:
(E1) `Tb = T` on `Lip_b × Lip^k`; (E2) `Tb` is linear in `h`; (E3) `Tb` is linear in each slot `πᵢ`;
(E4) `|Tb h π| ≤ ∏ Lip(πᵢ) ∫ |h| dμ` for every admissible mass measure `μ`. -/
def IsAKExtension {d k : ℕ} (T Tb : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ) : Prop :=
  (∀ f, IsBddLipFun f → ∀ π : Fin k → Vec d → ℝ, IsLipTuple π → Tb f π = T f π) ∧
  (∀ π : Fin k → Vec d → ℝ, IsLipTuple π → ∀ h g, IsBorelBdd h → IsBorelBdd g → ∀ a b : ℝ,
      Tb (a • h + b • g) π = a * Tb h π + b * Tb g π) ∧
  (∀ h, IsBorelBdd h → ∀ π : Fin k → Vec d → ℝ, IsLipTuple π → ∀ i ψ, IsLipFun ψ → ∀ a b : ℝ,
      Tb h (Function.update π i (a • π i + b • ψ)) =
        a * Tb h π + b * Tb h (Function.update π i ψ)) ∧
  (∀ μ, IsAKMassAdmissible T μ → ∀ h, IsBorelBdd h → ∀ (π : Fin k → Vec d → ℝ) (K : Fin k → ℝ≥0),
      (∀ i, IsEuclLipschitzWith (K i) (π i)) → |Tb h π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |h x| ∂μ)

end AFree
