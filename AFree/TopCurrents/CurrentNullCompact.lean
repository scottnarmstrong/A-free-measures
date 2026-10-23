module

public import AFree.TopCurrents.CurrentNullLin
public import AFree.TopCurrents.CurrentNullEst
public import AFree.Curves.Perturb
public import AFree.Curves

/-!
# Vanishing of `ν` on null sets, Step 1: `ν(K) = 0` for compact `C`-null `K`
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.Nu AFree.MetricCurrents.LipApprox

private lemma bddGrad_of_eucl {n m : ℕ} {C : ℝ≥0} {ψ : Fin n → Vec m → ℝ}
    (h : ∀ i, IsEuclLipschitzWith C (ψ i)) : ∃ M : ℝ, ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ M := by
  choose L hL using fun i => exists_lipschitzWith_of_eucl (h i)
  refine ⟨∑ i, (L i : ℝ), fun i y => ?_⟩
  exact (norm_fderiv_le_of_lipschitz ℝ (hL i)).trans
    (Finset.single_le_sum (f := fun i => (L i : ℝ)) (fun j _ => (L j).2) (Finset.mem_univ i))

private lemma rowTuple_eucl {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R * R.transpose = 1) {g : Vec (n + 1) → ℝ} {Γ : ℝ≥0} (hg : IsEuclLipschitzWith Γ g)
    (i : Fin (n + 1)) : IsEuclLipschitzWith (max 1 Γ) (rowTuple R g i) := by
  by_cases hi : i = Fin.last n
  · subst hi
    rw [rowTuple_last]
    exact isEucl_mono (le_max_right _ _) hg
  · rw [show rowTuple R g i = fun y => ∑ j, R i j * y j from funext (rowTuple_ne R g hi)]
    exact isEucl_mono (le_max_left _ _) (linRow_eucl R hR i)

private lemma rowTuple_contDiff {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {g : Vec (n + 1) → ℝ} (hg : ContDiff ℝ 1 g) (i : Fin (n + 1)) :
    ContDiff ℝ 1 (rowTuple R g i) := by
  by_cases hi : i = Fin.last n
  · subst hi
    rw [rowTuple_last]
    exact hg
  · rw [show rowTuple R g i = fun y => ∑ j, R i j * y j from funext (rowTuple_ne R g hi)]
    exact ContDiff.sum fun j _ =>
      contDiff_const.mul (contDiff_apply ℝ ℝ j)

/-- For `f ∈ Lip_b`: `T(f, ψ) = det R ∫ f D_e g dν` for the tuple
`ψ = rowTuple R g`. -/
theorem currentnull_perturbation_map {n : ℕ}
    {T : (Vec (n + 1) → ℝ) → (Fin (n + 1) → Vec (n + 1) → ℝ) → ℝ} (hT : IsMetricCurrent (n + 1) T)
    {ν : SignedMeasure (Vec (n + 1))} (hν : IsNuMeasure T ν)
    {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hR : R * R.transpose = 1) {e : Vec (n + 1)}
    (he : ∀ j, R (Fin.last n) j = e j) {g : Vec (n + 1) → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {Γ : ℝ≥0} (hgL : IsEuclLipschitzWith Γ g) {f : Vec (n + 1) → ℝ} (hf : IsBddLipFun f) :
    T f (rowTuple R g) = R.det * ∫ᵛ x, f x * fderiv ℝ g x e ∂•ν := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hJ := nu_jacobian_integral hT hν hf (rowTuple_contDiff R hg1)
    (bddGrad_of_eucl (rowTuple_eucl hR hgL))
  rw [hJ]
  have : (fun x => f x * jacDet (rowTuple R g) x) =
      fun x => R.det • (f x * fderiv ℝ g x e) := by
    funext x
    rw [jacDet_rowTuple R hR he, smul_eq_mul]
    ring
  rw [this, VectorMeasure.integral_fun_smul, smul_eq_mul]

/-- If `g_k → 0` pointwise, `0 ≤ g_k`, with a common Lipschitz
constant, then `T(f, ψ^k) → 0`. -/
theorem currentnull_limit_map_vanishes {n : ℕ}
    {T : (Vec (n + 1) → ℝ) → (Fin (n + 1) → Vec (n + 1) → ℝ) → ℝ} (hT : IsMetricCurrent (n + 1) T)
    {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hR : R * R.transpose = 1)
    {g : ℕ → Vec (n + 1) → ℝ} {Γ : ℝ≥0} (hgL : ∀ k, IsEuclLipschitzWith Γ (g k))
    (hg0 : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 0)) {f : Vec (n + 1) → ℝ} (hf : IsBddLipFun f) :
    Tendsto (fun k => T f (rowTuple R (g k))) atTop (𝓝 0) := by
  have hz : IsEuclLipschitzWith 0 (0 : Vec (n + 1) → ℝ) := by
    intro x y; simp
  have hlip : IsLipTuple (rowTuple R 0) := fun i => ⟨_, rowTuple_eucl hR hz i⟩
  have h0 : T f (rowTuple R 0) = 0 := by
    have hπ : IsLipTuple (fun (i : Fin (n + 1)) (y : Vec (n + 1)) => ∑ j, R i j * y j) :=
      fun i => ⟨1, linRow_eucl R hR i⟩
    exact (akbasic_slot_linear hT hf hπ (Fin.last n)).1
  have hlim := hT.2.2.2.2.1 f hf (rowTuple R 0) hlip (fun k => rowTuple R (g k))
    ⟨max 1 Γ, fun k i => rowTuple_eucl hR (hgL k) i⟩ (by
      intro i x
      by_cases hi : i = Fin.last n
      · subst hi
        simpa [rowTuple_last] using hg0 x
      · simp only [rowTuple_ne R _ hi]
        exact tendsto_const_nhds)
  rwa [h0] at hlim

end AFree
