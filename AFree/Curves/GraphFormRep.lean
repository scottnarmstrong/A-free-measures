module

public import AFree.Curves.GraphForm

/-!
# Every `C`-curve is a graph; `C`-nullness via the parameter

Every `C`-curve is a graph curve `γ_η`, so `C`-nullness can be tested through the parameter.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- Every `C`-curve `G` is of the form
`γ_η([u₀, u₁])` for a `tan α`-Lipschitz `η : [u₀, u₁] → e^⊥`. -/
theorem ccurve_exists_graph {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {G : Set (Vec d)} (hG : IsCCurve (cone e α) G) :
    ∃ u₀ u₁ : ℝ, ∃ η : ℝ → Vec d, u₀ ≤ u₁ ∧ IsConeGraphFn e α u₀ u₁ η ∧
      G = graphCurve e η '' Icc u₀ u₁ := by
  classical
  obtain ⟨a, b, hab, γ, ⟨⟨K, hK⟩, hd⟩, rfl⟩ := hG
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hinc := (ccurve_incr_iff (e := e) hα hα2 hab (hK.lipschitzOnWith (s := Icc a b))).mp hd
  set φ : ℝ → ℝ := fun s => vecDot (γ s) e with hφ
  set W : Vec d → Vec d := fun x => x - vecDot x e • e with hW
  have F1 : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s ≤ s' →
      φ s ≤ φ s' ∧ vecEuclideanNorm (γ s' - γ s) ≤ (φ s' - φ s) / Real.cos α := by
    intro s hs s' hs' h
    have hm := hinc s hs s' hs' h
    have hn := norm_le_of_mem_cone hα hα2 hm
    have hn0 : 0 ≤ vecDot (γ s' - γ s) e := by
      have : Real.cos α * vecEuclideanNorm (γ s' - γ s) ≤ vecDot (γ s' - γ s) e := hm
      nlinarith [vecEuclideanNorm_nonneg (γ s' - γ s)]
    rw [vecDot_sub_left] at hn hn0
    exact ⟨by simp only [hφ]; linarith, hn⟩
  have F2 : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, φ s = φ s' → γ s = γ s' := by
    have key : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s ≤ s' → φ s = φ s' → γ s = γ s' := by
      intro s hs s' hs' h he'
      have := (F1 s hs s' hs' h).2
      rw [← he', sub_self, zero_div] at this
      exact (sub_eq_zero.mp (vecEuclideanNorm_eq_zero_iff.mp
        (le_antisymm this (vecEuclideanNorm_nonneg _)))).symm
    intro s hs s' hs' h
    rcases le_total s s' with h1 | h1
    · exact key s hs s' hs' h1 h
    · exact (key s' hs' s hs h1 h.symm).symm
  have hcont : ContinuousOn φ (Icc a b) :=
    ((continuous_vecDot_left e).comp hK.continuous).continuousOn
  have hrange : ∀ u ∈ Icc (φ a) (φ b), ∃ s ∈ Icc a b, φ s = u := fun u hu =>
    intermediate_value_Icc hab hcont hu
  let η : ℝ → Vec d := fun u => if h : ∃ s ∈ Icc a b, φ s = u then W (γ (Classical.choose h)) else 0
  have hη : ∀ s ∈ Icc a b, η (φ s) = W (γ s) := by
    intro s hs
    have h : ∃ s' ∈ Icc a b, φ s' = φ s := ⟨s, hs, rfl⟩
    simp only [η, h, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    rw [F2 _ h1 s hs h2]
  have hWsub : ∀ x y : Vec d, W x - W y = (x - y) - vecDot (x - y) e • e := by
    intro x y; simp only [hW, vecDot_sub_left, sub_smul]; abel
  have hmain : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s ≤ s' →
      vecEuclideanNorm (η (φ s') - η (φ s)) ≤ Real.tan α * (φ s' - φ s) := by
    intro s hs s' hs' h
    rw [hη s hs, hη s' hs', hWsub]
    have := ((cone_iff he hα hα2 _).mp (hinc s hs s' hs' h)).2
    rw [vecDot_sub_left] at this
    rw [vecDot_sub_left]
    exact this
  have hφm : ∀ s ∈ Icc a b, φ a ≤ φ s ∧ φ s ≤ φ b := fun s hs =>
    ⟨(F1 a (left_mem_Icc.mpr hab) s hs hs.1).1, (F1 s hs b (right_mem_Icc.mpr hab) hs.2).1⟩
  refine ⟨φ a, φ b, η, (F1 a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab).1,
    ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    obtain ⟨s, hs, rfl⟩ := hrange u hu
    rw [hη s hs]
    exact vecDot_sub_dot_smul he _
  · intro u hu u' hu'
    obtain ⟨s, hs, rfl⟩ := hrange u hu
    obtain ⟨s', hs', rfl⟩ := hrange u' hu'
    rcases le_total s s' with h | h
    · have := hmain s hs s' hs' h
      have hle := (F1 s hs s' hs' h).1
      rw [vecEuclideanNorm_sub_comm, abs_sub_comm, abs_of_nonneg (by simp only [hφ] at hle ⊢; linarith)]
      exact this
    · have := hmain s' hs' s hs h
      have hle := (F1 s' hs' s hs h).1
      rw [abs_of_nonneg (by simp only [hφ] at hle ⊢; linarith)]
      exact this
  · ext x
    simp only [mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨φ s, hφm s hs |> fun h => ⟨h.1, h.2⟩, ?_⟩
      rw [graphCurve, hη s hs, hW]
      simp only [hφ]; abel
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨s, hs, rfl⟩ := hrange u hu
      refine ⟨s, hs, ?_⟩
      rw [graphCurve, hη s hs, hW]
      simp only [hφ]; abel

end AFree
