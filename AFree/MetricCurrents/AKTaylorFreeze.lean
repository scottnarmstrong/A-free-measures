module

public import AFree.MetricCurrents.AKTaylorExpand

/-!
# Taylor lemma, Step 2: freezing the Jacobian on one cube
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKTaylor

open PDE AFree

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ} {π : Fin k → Vec d → ℝ}
  {ψ : Fin k → Vec k → ℝ} {Λ M : ℝ≥0} {μ : Measure (Vec d)}

/-- The nearest-point projection onto the sup cube `{‖y - c‖ ≤ w}` (coordinatewise clamp). -/
def clampVec (c : Vec k) (w : ℝ) (y : Vec k) : Vec k := fun l => max (c l - w) (min (c l + w) (y l))

lemma clampVec_sub_le (c : Vec k) (w : ℝ) (y y' : Vec k) :
    ‖clampVec c w y - clampVec c w y'‖ ≤ ‖y - y'‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l => ?_
  have h1 : |min (c l + w) (y l) - min (c l + w) (y' l)| ≤ |y l - y' l| := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)
  have h2 : |clampVec c w y l - clampVec c w y' l| ≤ |y l - y' l| := by
    unfold clampVec
    rw [max_comm (c l - w), max_comm (c l - w)]
    exact (abs_max_sub_max_le_abs _ _ _).trans h1
  simpa [Real.norm_eq_abs] using h2.trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - y') l)

lemma norm_clampVec_sub_le (c : Vec k) {w : ℝ} (hw : 0 ≤ w) (y : Vec k) :
    ‖clampVec c w y - c‖ ≤ w := by
  refine (pi_norm_le_iff_of_nonneg hw).2 fun l => ?_
  simp only [clampVec, Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor
  · have := le_max_left (c l - w) (min (c l + w) (y l)); linarith
  · have : max (c l - w) (min (c l + w) (y l)) ≤ c l + w :=
      max_le (by linarith) (min_le_left _ _)
    linarith

lemma clampVec_eq_self (c : Vec k) {w : ℝ} {y : Vec k} (h : ‖y - c‖ ≤ w) : clampVec c w y = y := by
  funext l
  have h1 := (abs_le.1 (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - c) l |>.trans h :
    |y l - c l| ≤ w))
  simp only [clampVec]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- The remainder `e(z) = ψ_i(z) - ψ_i(c) - Dψ_i(c)(z - c)` composed with the clamp. -/
noncomputable def eTil (ψ : Fin k → Vec k → ℝ) (i : Fin k) (c : Vec k) (w : ℝ) (y : Vec k) : ℝ :=
  ψ i (clampVec c w y) - ψ i c - fderiv ℝ (ψ i) c (clampVec c w y - c)

/-- The tuple with constant Jacobian `τ_i = Dψ_i(c)(π) + ẽ_i ∘ π + (ψ_i(c) - Dψ_i(c) c)`. -/
noncomputable def tauTuple (ψ : Fin k → Vec k → ℝ) (π : Fin k → Vec d → ℝ) (c : Vec k) (w : ℝ) :
    Fin k → Vec d → ℝ :=
  fun i x => (fderiv ℝ (ψ i) c (evalTuple π x) + eTil ψ i c w (evalTuple π x)) +
    (ψ i c - fderiv ℝ (ψ i) c c)

lemma eTil_lip (cx : Ctx T π ψ Λ M μ) {δ : ℝ≥0} {c : Vec k} {w : ℝ} (hw : 0 ≤ w)
    (hδ : ∀ z, ‖z - c‖ ≤ w → ∀ i, ‖fderiv ℝ (ψ i) z - fderiv ℝ (ψ i) c‖ ≤ δ) (i : Fin k)
    (y y' : Vec k) : |eTil ψ i c w y - eTil ψ i c w y'| ≤ δ * ‖y - y'‖ := by
  set L := fderiv ℝ (ψ i) c
  have hdiff : ∀ z, DifferentiableAt ℝ (ψ i) z := fun z => (cx.hψ i).differentiable one_ne_zero z
  have hder : ∀ z, HasFDerivAt (fun z => ψ i z - ψ i c - L (z - c)) (fderiv ℝ (ψ i) z - L) z := by
    intro z
    have h1 := (hdiff z).hasFDerivAt.sub_const (ψ i c)
    have h2 : HasFDerivAt (fun z : Vec k => L (z - c)) L z := by
      have := L.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
      simpa [Function.comp_def] using this
    exact h1.sub h2
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun z => ψ i z - ψ i c - L (z - c))
    (s := Metric.closedBall c w) (C := (δ : ℝ)) (fun z _ => (hder z).differentiableAt)
    (fun z hz => by
      rw [(hder z).fderiv]
      exact hδ z (by simpa [dist_eq_norm] using hz) i)
    (convex_closedBall c w)
    (y := clampVec c w y) (x := clampVec c w y')
    (by simpa [dist_eq_norm] using norm_clampVec_sub_le c hw y')
    (by simpa [dist_eq_norm] using norm_clampVec_sub_le c hw y)
  have hc := clampVec_sub_le c w y y'
  unfold eTil
  simp only [Real.norm_eq_abs] at hb
  nlinarith [δ.coe_nonneg, mul_le_mul_of_nonneg_left hc δ.coe_nonneg]

lemma isLipFun_apply_eval (cx : Ctx T π ψ Λ M μ) (L : Vec k →L[ℝ] ℝ) {C : ℝ≥0} (hL : ‖L‖ ≤ C) :
    IsLipFun (fun x => L (evalTuple π x)) := by
  refine ⟨C * Λ, lip_comp cx.hπ (fun y => L y) C fun y y' => ?_⟩
  have := L.le_opNorm (y - y')
  rw [map_sub] at this
  simp only [Real.norm_eq_abs] at this
  nlinarith [norm_nonneg (y - y')]

lemma tauTuple_isLipTuple (cx : Ctx T π ψ Λ M μ) {δ : ℝ≥0} {c : Vec k} {w : ℝ} (hw : 0 ≤ w)
    (hδ : ∀ z, ‖z - c‖ ≤ w → ∀ i, ‖fderiv ℝ (ψ i) z - fderiv ℝ (ψ i) c‖ ≤ δ) :
    IsLipTuple (tauTuple ψ π c w) := fun i => by
  exact isLipFun_add_const (isLipFun_add (isLipFun_apply_eval cx _ (cx.hM i c)) ⟨_, lip_comp cx.hπ
    (eTil ψ i c w) δ (eTil_lip cx hw hδ i)⟩) _

/-- Step 2. If `{f ≠ 0}` lies in the open set `V = {x : ‖π(x) - c‖ <
w}` (with the cube `Q = {‖y - c‖ ≤ w}`, on which `Dψ` oscillates by at most `δ` around `Dψ(c)`), then
`τ` is a Lipschitz tuple, equal to `ψ ∘ π` on `V`, and `T(f, ψ ∘ π) = T(f, τ)`. -/
theorem freezing (cx : Ctx T π ψ Λ M μ) {δ : ℝ≥0} {c : Vec k} {w : ℝ} (hw : 0 ≤ w)
    (hδ : ∀ z, ‖z - c‖ ≤ w → ∀ i, ‖fderiv ℝ (ψ i) z - fderiv ℝ (ψ i) c‖ ≤ δ)
    {f : Vec d → ℝ} (hf : IsBddLipFun f) (hsupp : ∀ x, f x ≠ 0 → ‖evalTuple π x - c‖ < w) :
    IsLipTuple (tauTuple ψ π c w) ∧ T f (psiPi ψ π) = T f (tauTuple ψ π c w) := by
  refine ⟨tauTuple_isLipTuple cx hw hδ, ?_⟩
  refine akbasic_open_locality cx.hT hf (isLipTuple_psi cx) (tauTuple_isLipTuple cx hw hδ)
    (U := {x | ‖evalTuple π x - c‖ < w}) ?_ (fun x hx => hsupp x hx) ?_
  · exact isOpen_lt (continuous_norm.comp ((continuous_evalTuple cx.hπ).sub continuous_const))
      continuous_const
  · intro i x hx
    have hx' : ‖evalTuple π x - c‖ ≤ w := le_of_lt hx
    simp only [tauTuple, eTil, clampVec_eq_self c hx', psiPi]
    rw [map_sub]
    ring

end AFree.MetricCurrents.AKTaylor
