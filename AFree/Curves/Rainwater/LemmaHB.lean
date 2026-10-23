module

public import AFree.Curves.Rainwater.LemmaOne
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Rainwater's lemma: the convex combination, Hahn--Banach in `ℝ^m`)

The coordinates are indexed by the finite set `s` of the finite subcover.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace AFree

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompactSpace X] [BorelSpace X]

omit [CompactSpace X] in
lemma rainCost_eq (μ : Measure X) [IsFiniteMeasure μ] (f : X →ᵇ ℝ) (l : ProbabilityMeasure X) :
    rainCost μ f l = ∫ x, f x ∂μ + 1 - ∫ x, f x ∂(l : Measure X) := by
  unfold rainCost
  rw [integral_sub (integrable_const (1 : ℝ)) (f.integrable _)]
  simp
  ring

omit [CompactSpace X] in
lemma integral_comb (g : X →ᵇ ℝ) (a b : ℝ≥0) (m₁ m₂ : Measure X) [IsFiniteMeasure m₁]
    [IsFiniteMeasure m₂] :
    ∫ x, g x ∂(a • m₁ + b • m₂) = a * ∫ x, g x ∂m₁ + b * ∫ x, g x ∂m₂ := by
  rw [integral_add_measure (g.integrable _) (g.integrable _), integral_smul_nnreal_measure,
    integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, smul_eq_mul]

/-- If the finite family `s` from the finite subcover covers the convex compact
set `F` (every `λ ∈ F` has `⟨μ, f_i⟩ + ⟨λ, 1 - f_i⟩ < δ` for some `i`), then one convex combination
`f_δ = ∑ a_i f_i` of values in `[0, 1]` has `⟨μ, f_δ⟩ + ⟨λ, 1 - f_δ⟩ < δ` for every `λ ∈ F`
(Hahn--Banach in `ℝ^s`). -/
theorem rainwater_convex_combination (μ : Measure X) [IsFiniteMeasure μ]
    (F : Set (ProbabilityMeasure X)) (hF : IsCompact F)
    (hconv : Convex ℝ≥0 ((fun l : ProbabilityMeasure X => (l : Measure X)) '' F)) {δ : ℝ}
    (hδ : 0 < δ) (s : Finset (X →ᵇ ℝ)) (hs : ∀ f ∈ s, IsUnitFn f)
    (hcov : ∀ l ∈ F, ∃ f ∈ s, rainCost μ f l < δ) :
    ∃ f : X →ᵇ ℝ, IsUnitFn f ∧ ∀ l ∈ F, rainCost μ f l < δ := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨l₀, hl₀⟩
  · exact ⟨0, fun x => ⟨le_refl _, zero_le_one⟩, by simp⟩
  let z : ProbabilityMeasure X → (s → ℝ) := fun l i => rainCost μ i.1 l
  have hz : Continuous z := continuous_pi fun i => continuous_rainCost μ i.1
  let D : Set (s → ℝ) := z '' F
  let Q : Set (s → ℝ) := {q | ∀ i, δ ≤ q i}
  have hDc : IsCompact D := hF.image hz
  have hDv : Convex ℝ D := by
    rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩ a b ha hb hab
    have hab' : a.toNNReal + b.toNNReal = 1 := by
      apply NNReal.coe_injective
      simp [Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb, hab]
    obtain ⟨l, hl, hle⟩ := hconv (mem_image_of_mem _ h₁) (mem_image_of_mem _ h₂) zero_le zero_le hab'
    refine ⟨l, hl, ?_⟩
    funext i
    have hl' : (l : Measure X) = a.toNNReal • (l₁ : Measure X) + b.toNNReal • (l₂ : Measure X) :=
      hle
    simp only [z, rainCost_eq, hl', integral_comb]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.coe_toNNReal _ ha,
      Real.coe_toNNReal _ hb]
    obtain rfl : b = 1 - a := by linarith
    ring
  have hQv : Convex ℝ Q := by
    intro p hp q hq a b ha hb hab i
    have h1 := hp i
    have h2 := hq i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  have hQc : IsClosed Q := by
    have : Q = ⋂ i, {q : s → ℝ | δ ≤ q i} := by ext; simp [Q]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hdisj : Disjoint D Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨l, hl, rfl⟩ hq
    obtain ⟨f, hf, hlt⟩ := hcov l hl
    exact absurd (hq ⟨f, hf⟩) (not_le.2 hlt)
  obtain ⟨g, u, v, hgD, huv, hgQ⟩ := geometric_hahn_banach_compact_closed hDv hDc hQv hQc hdisj
  classical
  set a : s → ℝ := fun i => g fun j => if i = j then 1 else 0 with ha_def
  have hrep : ∀ q : s → ℝ, g q = ∑ i, q i * a i := fun q => by
    have := LinearMap.pi_apply_eq_sum_univ (g : (s → ℝ) →ₗ[ℝ] ℝ) q
    simpa [a] using this
  set S : ℝ := ∑ i, a i with hS
  have hnn : ∀ i, 0 ≤ a i := by
    intro i
    by_contra hneg
    push Not at hneg
    set N : ℝ := |δ * S - v| / (-a i) with hN
    have hN0 : 0 ≤ N := div_nonneg (abs_nonneg _) (by linarith)
    have hq : (fun j => δ + (if j = i then N else 0)) ∈ Q := fun j => by
      show δ ≤ δ + (if j = i then N else 0)
      split_ifs <;> linarith
    have h1 := hgQ _ hq
    rw [hrep] at h1
    have h2 : ∑ j, (δ + (if j = i then N else 0)) * a j = δ * S + N * a i := by
      simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, hS]
    have h3 : N * a i = -|δ * S - v| := by
      rw [hN]; field_simp
      rw [mul_div_assoc, div_self hneg.ne, mul_one]
    have := le_abs_self (δ * S - v)
    linarith
  have hδS : v < δ * S := by
    have h1 := hgQ (fun _ => δ) (fun _ => le_refl _)
    rw [hrep] at h1; rw [hS, Finset.mul_sum]; exact h1
  have hgz : ∀ l ∈ F, g (z l) < u := fun l hl => hgD _ ⟨l, hl, rfl⟩
  have hgz0 : ∀ l, 0 ≤ g (z l) := fun l => by
    rw [hrep]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (rainCost_nonneg μ (hs i.1 i.2) l) (hnn i)
  have hSpos : 0 < S := by
    by_contra h
    push Not at h
    nlinarith [hgz l₀ hl₀, hgz0 l₀]
  set w : s → ℝ := fun i => a i / S with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => div_nonneg (hnn i) hSpos.le
  have hw1 : ∑ i, w i = 1 := by
    rw [hw]; simp only; rw [← Finset.sum_div, ← hS, div_self hSpos.ne']
  let f : X →ᵇ ℝ := ∑ i : s, w i • (i.1 : X →ᵇ ℝ)
  have hfx : ∀ x, f x = ∑ i : s, w i * i.1 x := fun x => by simp [f]
  refine ⟨f, ?_, ?_⟩
  · intro x
    rw [hfx]
    refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (hs i.1 i.2 x).1, ?_⟩
    calc ∑ i : s, w i * i.1 x ≤ ∑ i : s, w i :=
          Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hw0 i) (hs i.1 i.2 x).2
      _ = 1 := hw1
  · intro l hl
    have hlin : ∀ (m : Measure X) [IsFiniteMeasure m],
        ∫ x, f x ∂m = ∑ i : s, w i * ∫ x, i.1 x ∂m := by
      intro m _
      simp_rw [hfx]
      rw [integral_finsetSum _ (fun i _ => ((i.1).integrable m).const_mul _)]
      simp_rw [integral_const_mul]
    have hcost : rainCost μ f l = ∑ i : s, w i * z l i := by
      simp only [z, rainCost_eq, hlin, mul_sub, mul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.sum_mul, hw1]
      simp
    have hgl : g (z l) = S * ∑ i : s, w i * z l i := by
      rw [hrep, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hw]; field_simp
    rw [hcost]
    have := hgz l hl
    have h5 : S * ∑ i : s, w i * z l i < S * δ := by nlinarith
    exact lt_of_mul_lt_mul_left h5 hSpos.le

end AFree
