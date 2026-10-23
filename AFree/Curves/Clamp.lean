module

public import AFree.Curves.Increments

/-!
# `C`-curves from maps Lipschitz on an interval

Replacing `γ` by `γ ∘ clamp_{[a, b]}` (as in the definition of `C`-curve) turns a map that is Lipschitz on `[a, b]`
with `γ' ∈ C` a.e. on `[a, b]` into a `C`-curve parametrization on all of `ℝ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- The clamp `ℝ → [a, b] ⊂ ℝ`. -/
def clampIcc (a b : ℝ) (x : ℝ) : ℝ := max a (min x b)

lemma clampIcc_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clampIcc a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma clampIcc_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) : clampIcc a b x = x := by
  simp [clampIcc, min_eq_left hx.2, max_eq_right hx.1]

lemma abs_clampIcc_sub_le {a b : ℝ} (hab : a ≤ b) (x y : ℝ) :
    |clampIcc a b x - clampIcc a b y| ≤ |x - y| := by
  have h := (LipschitzWith.projIcc hab).dist_le_mul x y
  have e : ∀ z : ℝ, ((Set.projIcc a b hab z : Icc a b) : ℝ) = clampIcc a b z := fun z => by
    simp [Set.projIcc, clampIcc, min_comm]
  rw [Subtype.dist_eq, e, e, Real.dist_eq, Real.dist_eq] at h
  simpa using h

lemma ae_mem_Ioo_restrict (a b : ℝ) : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∈ Ioo a b := by
  rw [ae_restrict_iff' measurableSet_Icc]
  have hne : ∀ x : ℝ, ∀ᵐ t : ℝ, t ≠ x := fun x => by
    rw [ae_iff]; simp
  filter_upwards [(hne a).and (hne b)] with t ht htm
  exact ⟨lt_of_le_of_ne htm.1 (Ne.symm ht.1), lt_of_le_of_ne htm.2 ht.2⟩

/-- A map that is Lipschitz on `[a, b]` with `γ' ∈ C` a.e. on `[a, b]` has `γ([a, b])` a `C`-curve. -/
lemma isCCurve_of_lipschitzOn {C : Set (Vec d)} {γ : ℝ → Vec d} {a b : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hγ : LipschitzOnWith K γ (Icc a b))
    (hd : ∀ᵐ s ∂(volume.restrict (Icc a b)), deriv γ s ∈ C) : IsCCurve C (γ '' Icc a b) := by
  refine ⟨a, b, hab, γ ∘ clampIcc a b, ⟨⟨K, ?_⟩, ?_⟩, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := hγ.dist_le_mul _ (clampIcc_mem hab x) _ (clampIcc_mem hab y)
    have h2 := abs_clampIcc_sub_le hab x y
    simp only [Function.comp]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ K.2)
    rw [Real.dist_eq, Real.dist_eq]; exact h2
  · filter_upwards [hd, ae_mem_Ioo_restrict a b] with s hs hs'
    have : (γ ∘ clampIcc a b) =ᶠ[𝓝 s] γ := by
      filter_upwards [Ioo_mem_nhds hs'.1 hs'.2] with x hx
      simp [clampIcc_of_mem (Ioo_subset_Icc_self hx)]
    rw [this.deriv_eq]; exact hs
  · ext y
    simp only [mem_image, Function.comp]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [clampIcc_of_mem hx]⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [clampIcc_of_mem hx]⟩

end AFree
