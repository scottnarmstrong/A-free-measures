module

public import AFree.Curves.Perturb.GraphFn
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform bounds and an Arzelà–Ascoli subsequence
-/

@[expose] public section

open MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ}

private lemma isCompact_perp_ball (e : Vec d) (M : ℝ) :
    IsCompact {v : Vec d | vecDot v e = 0 ∧ vecEuclideanNorm v ≤ M} := by
  refine (isCompact_closedBall (0 : Vec d) M).of_isClosed_subset ?_ ?_
  · exact (isClosed_eq (continuous_vecDot_left e) continuous_const).inter
      (isClosed_le continuous_vecEuclideanNorm continuous_const)
  · intro v hv
    rw [mem_closedBall_zero_iff]
    exact (norm_le_vecEuclideanNorm v).trans hv.2

/-- A sequence of `tan α`-Lipschitz maps into `e^⊥` on a compact
interval `[u₀, u₁]` that is bounded at one point of the interval for each `n` has a subsequence
converging pointwise (indeed uniformly) on `[u₀, u₁]` to a `tan α`-Lipschitz map into `e^⊥`. -/
theorem perturb_step1_compactness (hα : 0 ≤ Real.tan α) {u₀ u₁ M : ℝ} {ζ : ℕ → ℝ → Vec d}
    (hζ : ∀ n, IsConeGraphFn e α u₀ u₁ (ζ n))
    (hM : ∀ n, ∃ u ∈ Icc u₀ u₁, vecEuclideanNorm (ζ n u) ≤ M) :
    ∃ (φ : ℕ → ℕ) (ζ₀ : ℝ → Vec d), StrictMono φ ∧ IsConeGraphFn e α u₀ u₁ ζ₀ ∧
      ∀ u ∈ Icc u₀ u₁, Tendsto (fun n => ζ (φ n) u) atTop (𝓝 (ζ₀ u)) := by
  set t := Real.tan α with ht
  have : CompactSpace (Icc u₀ u₁) := isCompact_iff_compactSpace.mp isCompact_Icc
  set M' := M + t * (u₁ - u₀) with hM'
  set Y : Set (Vec d) := {v | vecDot v e = 0 ∧ vecEuclideanNorm v ≤ M'} with hY
  have hYc : IsCompact Y := isCompact_perp_ball e M'
  have hbound : ∀ n, ∀ u ∈ Icc u₀ u₁, ζ n u ∈ Y := by
    intro n u hu
    obtain ⟨v, hv, hvM⟩ := hM n
    refine ⟨(hζ n).1 u hu, ?_⟩
    have h1 := (hζ n).2 u hu v hv
    have h2 : |u - v| ≤ u₁ - u₀ := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
    have h3 : vecEuclideanNorm (ζ n u) ≤ vecEuclideanNorm (ζ n u - ζ n v) + vecEuclideanNorm (ζ n v) := by
      have := vecEuclideanNorm_add_le (ζ n u - ζ n v) (ζ n v)
      rwa [sub_add_cancel] at this
    nlinarith [mul_le_mul_of_nonneg_left h2 hα]
  let f : ℕ → (Icc u₀ u₁ →ᵇ Vec d) := fun n =>
    mkOfCompact ⟨fun x : Icc u₀ u₁ => ζ n x, ((hζ n).lipschitzOnWith hα).continuousOn.domRestrict⟩
  let A : Set (Icc u₀ u₁ →ᵇ Vec d) :=
    {g | (∀ x, g x ∈ Y) ∧ ∀ x y, vecEuclideanNorm (g x - g y) ≤ t * |(x : ℝ) - y|}
  have hfA : ∀ n, f n ∈ A := fun n =>
    ⟨fun x => hbound n x x.2, fun x y => (hζ n).2 x x.2 y y.2⟩
  have hAclosed : IsClosed A := by
    have : A = (⋂ x, {g : Icc u₀ u₁ →ᵇ Vec d | g x ∈ Y}) ∩
        ⋂ x, ⋂ y, {g : Icc u₀ u₁ →ᵇ Vec d | vecEuclideanNorm (g x - g y) ≤ t * |(x : ℝ) - y|} := by
      ext g; simp only [A, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [this]
    refine (isClosed_iInter fun x => hYc.isClosed.preimage (continuous_eval_const x)).inter
      (isClosed_iInter fun x => isClosed_iInter fun y => ?_)
    exact isClosed_le (continuous_vecEuclideanNorm.comp
      ((continuous_eval_const x).sub (continuous_eval_const y))) continuous_const
  have hequi : Equicontinuous ((↑) : A → Icc u₀ u₁ → Vec d) := by
    refine (LipschitzWith.uniformEquicontinuous (fun (g : A) (x : Icc u₀ u₁) => (g : Icc u₀ u₁ →ᵇ Vec d) x)
      (Real.toNNReal t) fun g => ?_).equicontinuous
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, Real.coe_toNNReal _ hα, Subtype.dist_eq, Real.dist_eq]
    exact (norm_le_vecEuclideanNorm _).trans (g.2.2 x y)
  have hcomp : IsCompact A :=
    arzela_ascoli₂ Y hYc A hAclosed (fun g x hg => hg.1 x) hequi
  obtain ⟨g, hgA, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hfA
  refine ⟨φ, fun u => if hu : u ∈ Icc u₀ u₁ then g ⟨u, hu⟩ else 0, hφ, ⟨fun u hu => ?_, fun u hu u' hu' => ?_⟩,
    fun u hu => ?_⟩
  · simpa [hu] using (hgA.1 ⟨u, hu⟩).1
  · simpa [hu, hu'] using hgA.2 ⟨u, hu⟩ ⟨u', hu'⟩
  · have key : Tendsto (fun n => (f (φ n)) ⟨u, hu⟩) atTop (𝓝 (g ⟨u, hu⟩)) :=
      ((continuous_eval_const (⟨u, hu⟩ : Icc u₀ u₁)).tendsto g).comp hlim
    have hg : (fun u => if hu : u ∈ Icc u₀ u₁ then g ⟨u, hu⟩ else (0 : Vec d)) u = g ⟨u, hu⟩ := by
      simp [hu]
    rw [hg]; exact key

end AFree
