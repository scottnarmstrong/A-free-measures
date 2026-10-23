module

public import AFree.Curves.Perturb.GraphFn

/-!
# The function `g` of [AM, Proposition 7.4]: definition and elementary facts

`perturbG e α A x = sup_{(a, b, η) ∈ Γ_x} (𝓛¹{u ∈ [a, b] : γ_η(u) ∈ A} - (b - x ⬝ e))`, with
`Γ_x` the triples `a ≤ b`, `b ≥ x ⬝ e`, `η` `tan α`-Lipschitz into `e^⊥` on `[a, b]` and
`η(b) = x_W = x - (x ⬝ e) e`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ}

/-- The parameter set measure `𝓛¹{u ∈ [a, b] : γ_η(u) ∈ A}`. -/
noncomputable def perturbMeas (e : Vec d) (A : Set (Vec d)) (a b : ℝ) (η : ℝ → Vec d) : ℝ≥0∞ :=
  volume (Icc a b ∩ {u | graphCurve e η u ∈ A})

/-- The set of values `m_A(η) - (b - x ⬝ e)` over `(a, b, η) ∈ Γ_x`. -/
def perturbVals (e : Vec d) (α : ℝ) (A : Set (Vec d)) (x : Vec d) : Set ℝ :=
  {r | ∃ (a b : ℝ) (η : ℝ → Vec d), a ≤ b ∧ vecDot x e ≤ b ∧ IsConeGraphFn e α a b η ∧
    η b = x - vecDot x e • e ∧ r = (perturbMeas e A a b η).toReal - (b - vecDot x e)}

/-- The function `g` of the proof of [AM, Proposition 7.4]. -/
noncomputable def perturbG (e : Vec d) (α : ℝ) (A : Set (Vec d)) (x : Vec d) : ℝ :=
  sSup (perturbVals e α A x)

lemma perturbMeas_lt_top (e : Vec d) (A : Set (Vec d)) (a b : ℝ) (η : ℝ → Vec d) :
    perturbMeas e A a b η < ⊤ :=
  (measure_mono inter_subset_left).trans_lt measure_Icc_lt_top

lemma perturb_dot_add_smul {e : Vec d} (he : vecEuclideanNorm e = 1) (x : Vec d) (s : ℝ) :
    vecDot (x + s • e) e = vecDot x e + s := by
  have he2 : vecNormSq e = 1 := by
    have := vecEuclideanNorm_sq e; rw [he] at this; linarith
  rw [vecDot_add_left, vecDot_smul_left, vecDot_self, he2]; ring

lemma perturb_wPart_add_smul {e : Vec d} (he : vecEuclideanNorm e = 1) (x : Vec d) (s : ℝ) :
    (x + s • e) - vecDot (x + s • e) e • e = x - vecDot x e • e := by
  rw [perturb_dot_add_smul he, add_smul]; abel

lemma perturb_dot_add_perp {e : Vec d} {v : Vec d} (hv : vecDot v e = 0) (x : Vec d) :
    vecDot (x + v) e = vecDot x e := by
  rw [vecDot_add_left, hv, add_zero]

lemma perturb_wPart_add_perp {e : Vec d} {v : Vec d} (hv : vecDot v e = 0) (x : Vec d) :
    (x + v) - vecDot (x + v) e • e = (x - vecDot x e • e) + v := by
  rw [perturb_dot_add_perp hv]; abel

lemma perturb_wPart_perp {e : Vec d} (he : vecEuclideanNorm e = 1) (x : Vec d) :
    vecDot (x - vecDot x e • e) e = 0 := vecDot_sub_dot_smul he x

lemma perturbVals_nonempty (he : vecEuclideanNorm e = 1) (hα : 0 ≤ Real.tan α) (A : Set (Vec d))
    (x : Vec d) : (0 : ℝ) ∈ perturbVals e α A x := by
  refine ⟨vecDot x e, vecDot x e, fun _ => x - vecDot x e • e, le_rfl, le_rfl,
    isConeGraphFn_const hα _ _ (perturb_wPart_perp he x), rfl, ?_⟩
  have : perturbMeas e A (vecDot x e) (vecDot x e) (fun _ => x - vecDot x e • e) = 0 :=
    measure_mono_null (inter_subset_left.trans (by simp)) (by simp : volume ({vecDot x e} : Set ℝ) = 0)
  simp [this]

lemma perturbVals_bddAbove {A : Set (Vec d)} {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ a b η, IsConeGraphFn e α a b η → perturbMeas e A a b η ≤ ENNReal.ofReal ε)
    (x : Vec d) : BddAbove (perturbVals e α A x) := by
  refine ⟨ε, ?_⟩
  rintro r ⟨a, b, η, hab, hxb, hη, -, rfl⟩
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hA a b η hη)
  rw [ENNReal.toReal_ofReal hε] at this
  linarith

end AFree
