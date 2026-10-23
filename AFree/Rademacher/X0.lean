module

public import AFree.Defs
public import AFree.Rademacher.Dot
public import PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Frames and the class `X₀(e)`

Frames, the class `X₀(e)` of smooth bounded functions with gradient bounded along the frame, and its Lipschitz bounds.
-/

@[expose] public section

open PDE Filter Topology
open scoped NNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- The Euclidean gradient `∇f(x) = (∂₁f(x), …, ∂_d f(x))` as a vector of `ℝ^d`. -/
noncomputable def euclGrad (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => euclideanCoordDeriv i f x

theorem vecDot_euclGrad (f : Vec d → ℝ) (x w : Vec d) :
    vecDot (euclGrad f x) w = fderiv ℝ f x w := by
  conv_rhs => rw [← sum_smul_basisVec w]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, vecDot, euclGrad, euclideanCoordDeriv]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- A *frame* is a continuous `e = (e₁, …, e_d) : ℝ^d → (ℝ^d)^d` with `e₁(x), …, e_d(x)`
an orthonormal basis for every `x` (an orthonormal `d`-tuple of `ℝ^d` is a basis). -/
def IsFrame (e : Vec d → Fin d → Vec d) : Prop :=
  Continuous e ∧ ∀ x k l, vecDot (e x k) (e x l) = if k = l then 1 else 0

/-- The class `X₀(e) = {f : ℝ^d → ℝ smooth, bounded, |∇f(x) · e_j(x)| ≤ 1 ∀ x j}`
(smoothness is `ContDiff ℝ (⊤ : ℕ∞)`). -/
def X0 (e : Vec d → Fin d → Vec d) : Set (Vec d → ℝ) :=
  {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ (∃ C : ℝ, ∀ x, |f x| ≤ C) ∧
    ∀ x j, |vecDot (euclGrad f x) (e x j)| ≤ 1}

theorem X0_differentiableAt {e : Vec d → Fin d → Vec d} {f : Vec d → ℝ} (hf : f ∈ X0 e)
    (x : Vec d) : DifferentiableAt ℝ f x :=
  (hf.1.differentiable (by simp)) x

private theorem euclGrad_norm_le {e : Vec d → Fin d → Vec d} (he : IsFrame e) {f : Vec d → ℝ}
    (hf : f ∈ X0 e) (x : Vec d) : vecEuclideanNorm (euclGrad f x) ≤ Real.sqrt d := by
  have hsum := sum_sq_vecDot_eq_vecNormSq (e := e x) (he.2 x) (euclGrad f x)
  have hle : ∑ j, vecDot (euclGrad f x) (e x j) ^ 2 ≤ d := by
    calc ∑ j, vecDot (euclGrad f x) (e x j) ^ 2 ≤ ∑ _j : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact (sq_le_one_iff_abs_le_one _).2 (hf.2.2 x j)
      _ = d := by simp
  unfold vecEuclideanNorm
  exact Real.sqrt_le_sqrt (hsum ▸ hle)

private theorem abs_sub_le_sqrt_mul {e : Vec d → Fin d → Vec d} (he : IsFrame e) {f : Vec d → ℝ}
    (hf : f ∈ X0 e) (x y : Vec d) :
    |f x - f y| ≤ Real.sqrt d * vecEuclideanNorm (x - y) := by
  set g : ℝ → ℝ := fun t => f (y + t • (x - y)) with hg
  have hdiff : ∀ t, HasDerivAt g (fderiv ℝ f (y + t • (x - y)) (x - y)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => y + t • (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
    exact (X0_differentiableAt hf _).hasFDerivAt.comp_hasDerivAt t h1
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖fderiv ℝ f (y + t • (x - y)) (x - y)‖ ≤
      Real.sqrt d * vecEuclideanNorm (x - y) := by
    intro t _
    rw [← vecDot_euclGrad f _ _, Real.norm_eq_abs]
    calc |vecDot (euclGrad f (y + t • (x - y))) (x - y)|
        ≤ vecEuclideanNorm (euclGrad f (y + t • (x - y))) * vecEuclideanNorm (x - y) :=
          abs_vecDot_le_vecEuclideanNorm_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (euclGrad_norm_le he hf _) (vecEuclideanNorm_nonneg _)
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
    (f' := fun t => fderiv ℝ f (y + t • (x - y)) (x - y))
    (fun t _ => (hdiff t).hasDerivWithinAt) hbound 1 (Set.right_mem_Icc.2 zero_le_one)
  simpa [hg, Real.norm_eq_abs] using this

/-- For `f ∈ X₀(e)`: `|∇f(x)| ≤ √d` everywhere; `f` is `√d`-Lipschitz for the
Euclidean norm and `d`-Lipschitz for the max norm; a uniform limit of members of `X₀(e)` is
`d`-Lipschitz for the max norm. -/
theorem X0_lipschitz {e : Vec d → Fin d → Vec d} (he : IsFrame e) :
    (∀ f ∈ X0 e, ∀ x, vecEuclideanNorm (euclGrad f x) ≤ Real.sqrt d) ∧
    (∀ f ∈ X0 e, IsEuclLipschitzWith (NNReal.sqrt d) f) ∧
    (∀ f ∈ X0 e, LipschitzWith (d : ℝ≥0) f) ∧
    (∀ (fs : ℕ → Vec d → ℝ) (f : Vec d → ℝ), (∀ j, fs j ∈ X0 e) →
      TendstoUniformly fs f atTop → LipschitzWith (d : ℝ≥0) f) := by
  have hd : ∀ f ∈ X0 e, LipschitzWith (d : ℝ≥0) f := by
    intro f hf
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm]
    calc |f x - f y| ≤ Real.sqrt d * vecEuclideanNorm (x - y) := abs_sub_le_sqrt_mul he hf x y
      _ ≤ Real.sqrt d * (Real.sqrt d * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (vecEuclideanNorm_le_sqrt_natCast_mul_norm _) (Real.sqrt_nonneg _)
      _ = ((d : ℝ≥0) : ℝ) * ‖x - y‖ := by
          rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg d)]; simp
  refine ⟨fun f hf x => euclGrad_norm_le he hf x, fun f hf x y => ?_, hd, ?_⟩
  · simpa using abs_sub_le_sqrt_mul he hf x y
  · intro fs f hfs hconv
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hx := hconv.tendsto_at x
    have hy := hconv.tendsto_at y
    have hlim : Tendsto (fun j => dist (fs j x) (fs j y)) atTop (𝓝 (dist (f x) (f y))) :=
      hx.dist hy
    refine le_of_tendsto' hlim fun j => ?_
    simpa using (hd _ (hfs j)).dist_le_mul x y

end AFree.Rademacher
