module

public import AFree.MetricCurrents

/-!
# Minors and the current `u_#`

Shared vocabulary:

* `minorDet F r c x`: the minor `M_{I,J}(F)(x) = det (∂_{c b} F_{r a} (x))_{a,b}`, `F : Fin m → Vec d → ℝ`,
  `r : Fin s → Fin m`, `c : Fin s → Fin d` (for `I = {i₁ < ⋯ < i_s}`, `J = {j₁ < ⋯ < j_s}` take `r, c` the
  increasing enumerations); `minorDet F r c x = 1` when `s = 0`; junk value from `fderiv` off the
  differentiability set;
* `usharp u`: `u_#(f, π) = ∫ f u det Dπ dx` ([AK, Example 3.2]);
* `uMass u = |u| 𝓛^d`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE

/-- The minor `M_{I,J}(F)(x) = det (∂_{c b} F_{r a}(x))_{a,b=1}^s` of the Jacobian of `F`. -/
noncomputable def minorDet {d m s : ℕ} (F : Fin m → Vec d → ℝ) (r : Fin s → Fin m)
    (c : Fin s → Fin d) (x : Vec d) : ℝ :=
  ((jacMat F x).submatrix r c).det

/-- `u_#(f, π) = ∫ f u det Dπ dx` ([AK, Example 3.2]), with `Dπ(x) = fderiv π x` arranged
as the matrix with rows `∇π_i(x)` (`jacDet`; junk value `0` off the differentiability set, which is
null for `π ∈ Lip^d`). -/
noncomputable def usharp {d : ℕ} (u : Vec d → ℝ) :
    (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ :=
  fun f π => ∫ x, f x * u x * jacDet π x

/-- The measure `|u| 𝓛^d`. -/
noncomputable def uMass {d : ℕ} (u : Vec d → ℝ) : Measure (Vec d) :=
  volume.withDensity fun x => ENNReal.ofReal |u x|

lemma minorDet_full {d : ℕ} (F : Fin d → Vec d → ℝ) (x : Vec d) :
    minorDet F id id x = jacDet F x := by
  simp [minorDet, jacDet]

end AFree
