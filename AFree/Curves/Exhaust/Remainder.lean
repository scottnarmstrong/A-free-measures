module

public import AFree.Curves.Exhaust.Alt

/-!
# Exhaustion, part 3: the remainder is a Borel `C`-null set
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- If `A₀ ∈ 𝔄` is maximal (with `μ⌞A₀ ≪ [ρ₀]`), there is a Borel
`C`-null set `N` (`C = C(e, α)`) with `μ⌞Nᶜ ≪ [ρ₀]`. -/
theorem exhaust_remainder {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {μ : Measure (Vec d)} [IsFiniteMeasure μ] {A₀ : Set (Vec d)}
    (hA₀ : IsExhaustible e α μ A₀) (hmax : ∀ A, IsExhaustible e α μ A → μ A ≤ μ A₀)
    {ρ₀ : Measure (ccurveSpace e α)} (hρ₀ : μ.restrict A₀ ≪ curveMix (ccurveSpace e α) ρ₀) :
    ∃ N : Set (Vec d), MeasurableSet N ∧ IsCNull (cone e α) N ∧
      μ.restrict Nᶜ ≪ curveMix (ccurveSpace e α) ρ₀ := by
  choose E hEm hE0 hEy using fun k => exhaust_alt_i hA₀ hmax k
  have hAm : MeasurableSet A₀ᶜ := hA₀.1.compl
  let N : Set (Vec d) := ⋃ k : ℕ, (Subtype.val '' E k ∩ euclideanClosedBall 0 (k : ℝ))
  have hNm : MeasurableSet N := MeasurableSet.iUnion fun k =>
    ((measurableSet_curveBall k).subtype_image (hEm k)).inter
      (isClosed_euclideanClosedBall _ _).measurableSet
  have hnull : IsCNull (cone e α) N := by
    refine isCNull_iUnion fun k => fun G hG => ?_
    refine (ccurve_cut he hα hα2 hG k).2 (Subtype.val '' E k) fun ζ hζ => ?_
    have h1 := hEy k ⟨ζ, hζ⟩
    have hc : Continuous fun s : I =>
        (⟨(ζ : C(I, Vec d)) s, mem_curveBall hζ s⟩ : curveBall d k) :=
      (ζ : C(I, Vec d)).continuous.subtype_mk _
    change Measure.map _ volume (E k) = 0 at h1
    rw [Measure.map_apply hc.measurable (hEm k)] at h1
    convert h1 using 2
    ext s
    constructor
    · rintro ⟨x, hx, hxs⟩
      have : x = ⟨(ζ : C(I, Vec d)) s, mem_curveBall hζ s⟩ := Subtype.ext hxs
      rw [this] at hx
      exact hx
    · intro hs
      exact ⟨_, hs, rfl⟩
  have hrem : μ (A₀ᶜ \ N) = 0 := by
    have hcov : A₀ᶜ \ N ⊆ ⋃ k : ℕ, (Subtype.val '' (E k)ᶜ ∩ exhaustPiece A₀ᶜ k) := by
      intro x hx
      obtain ⟨k, hk⟩ := exists_nat_ge (vecEuclideanNorm x)
      have hxb : x ∈ euclideanClosedBall (0 : Vec d) (k : ℝ) := by
        rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity), sub_zero]; exact hk
      have hxP : x ∈ exhaustPiece A₀ᶜ k := ⟨hx.1, hxb⟩
      have hxc := exhaustPiece_subset_curveBall _ k hxP
      refine mem_iUnion.2 ⟨k, ⟨⟨x, hxc⟩, ?_, rfl⟩, hxP⟩
      intro hxE
      exact hx.2 (mem_iUnion.2 ⟨k, ⟨⟨x, hxc⟩, hxE, rfl⟩, hxb⟩)
    refine measure_mono_null hcov (measure_iUnion_null fun k => ?_)
    have := hE0 k
    rwa [pieceMeasure_apply μ hAm] at this
  refine ⟨N, hNm, hnull, fun S hS => ?_⟩
  rw [Measure.restrict_apply' hNm.compl]
  have h1 : μ (S ∩ A₀) = 0 := by
    have := hρ₀ hS
    rwa [Measure.restrict_apply' hA₀.1] at this
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 hrem)
  by_cases hxA : x ∈ A₀
  · exact Or.inl ⟨hx.1, hxA⟩
  · exact Or.inr ⟨hxA, hx.2⟩

end AFree
