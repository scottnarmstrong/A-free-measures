module

public import AFree.Curves.Dichotomy
public import AFree.Rademacher.Dot

/-!
# AM Proposition 4.10: wide cones

Auxiliary facts for the proof of [AM, Proposition 4.10].
-/

@[expose] public section

open PDE MeasureTheory Set
open scoped ENNReal NNReal unitInterval

namespace AFree.Rademacher

variable {d : ℕ}

/-- Case (i): if `μ(F \ N) = 0` with `N` measurable and
`C`-null, then `F' = F ∩ N` is measurable, `C`-null and has `μ F' = μ F`. -/
theorem wideconenull_case_concentrated {μ : Measure (Vec d)} {C : Set (Vec d)} {F N : Set (Vec d)}
    (hF : MeasurableSet F) (hN : MeasurableSet N) (hNnull : IsCNull C N) (hμ : μ (F \ N) = 0) :
    F ∩ N ⊆ F ∧ MeasurableSet (F ∩ N) ∧ IsCNull C (F ∩ N) ∧ μ (F ∩ N) = μ F := by
  refine ⟨inter_subset_left, hF.inter hN, hNnull.mono inter_subset_right, ?_⟩
  rw [← measure_inter_add_sdiff F hN, hμ, add_zero]

/-- A rectifiable family for `μ.restrict F` is a
rectifiable family for `μ`. -/
theorem wideconenull_family_rectifiable {μ : Measure (Vec d)} {F : Set (Vec d)}
    {E : I → Set (Vec d)} (h : IsRectifiableFamily (μ.restrict F) E) : IsRectifiableFamily μ E := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun A hA hμA => h4 A hA ?_⟩
  exact le_antisymm (((Measure.le_iff'.1 Measure.restrict_le_self) A).trans hμA.le) bot_le

/-- For a rectifiable family for `μ` and a measurable
`μ`-null `Z`: `𝓗¹(E_t ∩ Z) = 0` for a.e. `t`. -/
theorem wideconenull_exceptional_null_set {μ : Measure (Vec d)} {E : I → Set (Vec d)}
    (h : IsRectifiableFamily μ E) {Z : Set (Vec d)} (hZ : MeasurableSet Z) (hμZ : μ Z = 0) :
    ∀ᵐ t : I, euclideanHausdorffOne d (E t ∩ Z) = 0 := by
  have h0 := h.2.2.2 Z hZ hμZ
  have hm := h.2.1 Z hZ
  exact (lintegral_eq_zero_iff hm).1 h0

/-- The arc test null set: if `t` passes the test of
`IsDecompTestField` for the arc `(γ, J)`, then the set `B_{t,γ}` of points of `E_t ∩ γ(J)` at which
some tangent `γ'(s)` is not in `V(x)` is `𝓗¹`-null. -/
theorem wideconenull_arc_test {V : Vec d → Submodule ℝ (Vec d)} {Et : Set (Vec d)}
    {γ : ℝ → Vec d} {J : Set ℝ}
    (h : ∀ᵐ x ∂(euclideanHausdorffOne d).restrict (Et ∩ γ '' J),
      ∀ s ∈ J, γ s = x → deriv γ s ∈ V x) :
    euclideanHausdorffOne d {x ∈ Et ∩ γ '' J | ∃ s ∈ J, γ s = x ∧ deriv γ s ∉ V x} = 0 := by
  have h0 : (euclideanHausdorffOne d).restrict (Et ∩ γ '' J)
      {x | ¬ ∀ s ∈ J, γ s = x → deriv γ s ∈ V x} = 0 := h
  refine le_antisymm ?_ bot_le
  calc euclideanHausdorffOne d {x ∈ Et ∩ γ '' J | ∃ s ∈ J, γ s = x ∧ deriv γ s ∉ V x}
      = euclideanHausdorffOne d ({x ∈ Et ∩ γ '' J | ∃ s ∈ J, γ s = x ∧ deriv γ s ∉ V x} ∩
          (Et ∩ γ '' J)) := by
        congr 1; ext x; simp only [mem_ofPred_eq, mem_inter_iff]; tauto
    _ ≤ (euclideanHausdorffOne d).restrict (Et ∩ γ '' J)
          {x ∈ Et ∩ γ '' J | ∃ s ∈ J, γ s = x ∧ deriv γ s ∉ V x} :=
        Measure.le_restrict_apply _ _
    _ ≤ (euclideanHausdorffOne d).restrict (Et ∩ γ '' J)
          {x | ¬ ∀ s ∈ J, γ s = x → deriv γ s ∈ V x} := by
        refine measure_mono fun x hx => ?_
        obtain ⟨-, s, hs, hγ, hn⟩ := hx
        exact fun hall => hn (hall s hs hγ)
    _ = 0 := h0

end AFree.Rademacher
