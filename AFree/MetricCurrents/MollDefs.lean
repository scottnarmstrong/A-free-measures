module

public import AFree.MetricCurrents.Basic
public import AFree.Analysis.Bump

/-!
# Definitions for the mollification of Lipschitz functions
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace AFree

open PDE

/-- A mollifier kernel: `ρ ∈ C_c^∞(ℝ^d)`, `ρ ≥ 0`, `∫ ρ = 1`, `spt ρ ⊆ {|z|_∞ ≤ 1}` (the closed ball
of the maximum norm on `Vec d`). -/
structure IsMollifierKernel {d : ℕ} (ρ : Vec d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ρ
  compact : HasCompactSupport ρ
  nonneg : ∀ z, 0 ≤ ρ z
  integral_eq_one : ∫ z, ρ z = 1
  tsupport_subset : tsupport ρ ⊆ Metric.closedBall 0 1

/-- The rescaled kernel `ρ_ε(z) = ε^{-d} ρ(z/ε)`. -/
noncomputable def scaledKernel {d : ℕ} (ρ : Vec d → ℝ) (ε : ℝ) (z : Vec d) : ℝ :=
  (ε⁻¹) ^ d * ρ (ε⁻¹ • z)

/-- The mollification `F^ε(x) = (F * ρ_ε)(x) = ∫ F(x - z) ρ_ε(z) dz` (Lebesgue measure). -/
noncomputable def mollLip {d : ℕ} (ρ : Vec d → ℝ) (ε : ℝ) (F : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ z, F (x - z) * scaledKernel ρ ε z

/-- The `j`-th partial derivative `∂_j F(x)` (the junk value `0` where `F` is not differentiable). -/
noncomputable def partialDeriv {d : ℕ} (F : Vec d → ℝ) (x : Vec d) (j : Fin d) : ℝ :=
  fderiv ℝ F x (Pi.single j 1)

end AFree
