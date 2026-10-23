module

public import AFree.Rademacher.FrameSteps3

/-!
# A continuous frame adapted to `V` on a compact set

The proof has five steps: `frame_pContinuous`, `frame_mColumns`, `frame_completion`, `frame_smallOscillation` and
`frame_tietzeExtension`; this file assembles them.
-/

@[expose] public section

open PDE MeasureTheory Filter Topology Matrix

namespace AFree.Rademacher

variable {d : ℕ}

/-- The linear functional `u ↦ u · g`. -/
def vecDotLeft (g : Vec d) : Vec d →ₗ[ℝ] ℝ where
  toFun u := vecDot u g
  map_add' x y := vecDot_add_left x y g
  map_smul' c x := by simp [vecDot_smul_left]

/-- Parseval for the orthonormal `m`-tuple `e_0, …, e_{m-1}` spanning `W^⊥`:
`∑_{k<m} (ε_i · e_k)² = |(Id - P) ε_i|²`. -/
theorem sum_sq_vecDot_basis_eq {P : Matrix (Fin d) (Fin d) ℝ} {W : Submodule ℝ (Vec d)}
    (hT : P.transpose = P) (hI : P * P = P) (hR : LinearMap.range (Matrix.toLin' P) = W)
    {e : Fin d → Vec d} (he : ∀ k l, vecDot (e k) (e l) = if k = l then 1 else 0) {m : ℕ}
    (hspan : Submodule.span ℝ (e '' {k : Fin d | (k : ℕ) < m}) = vperp W) (i : Fin d) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin d => (k : ℕ) < m), vecDot (basisVec i) (e k) ^ 2 =
      vecNormSq ((1 - P) *ᵥ basisVec i) := by
  set w : Vec d := (1 - P) *ᵥ basisVec i with hw
  have hwperp : w ∈ vperp W := by
    rw [← range_one_sub_eq_vperp hT hI hR]
    exact ⟨basisVec i, by rw [Matrix.toLin'_apply]⟩
  have hekperp : ∀ k : Fin d, (k : ℕ) < m → e k ∈ vperp W := fun k hk =>
    hspan ▸ Submodule.subset_span ⟨k, hk, rfl⟩
  have hQe : ∀ k : Fin d, (k : ℕ) < m → (1 - P) *ᵥ e k = e k := fun k hk => by
    have := (mem_vperp_iff_mulVec_eq_zero hT hI hR _).1 (hekperp k hk)
    rw [sub_mulVec, one_mulVec, this, sub_zero]
  have hT' : (1 - P).transpose = 1 - P := by rw [transpose_sub, transpose_one, hT]
  have hin : ∀ k : Fin d, (k : ℕ) < m → vecDot w (e k) = vecDot (basisVec i) (e k) := by
    intro k hk
    rw [hw, ← vecDot_mulVec_symm hT', hQe k hk]
  have hout : ∀ j : Fin d, ¬ (j : ℕ) < m → vecDot w (e j) = 0 := by
    intro j hj
    have hle : Submodule.span ℝ (e '' {k : Fin d | (k : ℕ) < m}) ≤ LinearMap.ker (vecDotLeft (e j)) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      show vecDot (e k) (e j) = 0
      simp [he k j, hkj]
    have : w ∈ LinearMap.ker (vecDotLeft (e j)) := hle (hspan ▸ hwperp)
    exact this
  have hpars := sum_sq_vecDot_eq_vecNormSq he w
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin d => (k : ℕ) < m)] at hpars
  have h0 : ∑ j ∈ Finset.univ.filter (fun k : Fin d => ¬ (k : ℕ) < m), vecDot w (e j) ^ 2 = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hout j (Finset.mem_filter.1 hj).2]; simp
  rw [h0, add_zero] at hpars
  rw [← hpars]
  exact Finset.sum_congr rfl fun k hk => by rw [hin k (Finset.mem_filter.1 hk).2]

/-- A continuous frame adapted to `V` on a compact set. Let `μ` be finite and `V`
have projections `P` (`IsBorelProj V P`, the witness form of `IsBorelSubspaceField V`), `v = ε_i`,
`δ > 0`, and `G` Borel with `μ G > 0` such that `rank (Id - P x) = m` and
`|(Id - P x) v| ≥ δ` for `x ∈ G`. Then there are a compact `E ⊆ G` with `μ E > 0` and a frame `e`
such that for `x ∈ E`: `e_0(x), …, e_{m-1}(x)` is a basis of `V(x)^⊥` (orthonormal and spanning),
so `e_k(x) ⊥ V(x)` and `∑_{k<m} (v · e_k(x))² = |(Id - P x) v|² ≥ δ²`. (The conditions `d ≥ 1` and
`m ∈ {1, …, d}` follow from the hypotheses and are not assumed; indices are `0`-based.) -/
theorem lem_frame (μ : Measure (Vec d)) [IsFiniteMeasure μ] {V : Vec d → Submodule ℝ (Vec d)}
    {P : Vec d → Matrix (Fin d) (Fin d) ℝ} (hP : IsBorelProj V P) (i : Fin d) {m : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {G : Set (Vec d)} (hG : MeasurableSet G) (hμG : 0 < μ G)
    (hrank : ∀ x ∈ G, (1 - P x).rank = m)
    (hproj : ∀ x ∈ G, δ ≤ vecEuclideanNorm ((1 - P x) *ᵥ basisVec i)) :
    ∃ E ⊆ G, IsCompact E ∧ 0 < μ E ∧ ∃ e : Vec d → Fin d → Vec d, IsFrame e ∧ ∀ x ∈ E,
      (∀ k : Fin d, (k : ℕ) < m → ∀ w ∈ V x, vecDot (e x k) w = 0) ∧
      Submodule.span ℝ (e x '' {k : Fin d | (k : ℕ) < m}) = vperp (V x) ∧
      ∑ k ∈ Finset.univ.filter (fun k : Fin d => (k : ℕ) < m), vecDot (basisVec i) (e x k) ^ 2 =
        vecNormSq ((1 - P x) *ᵥ basisVec i) ∧
      δ ^ 2 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin d => (k : ℕ) < m),
        vecDot (basisVec i) (e x k) ^ 2 := by
  have hmd : m ≤ d := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hμG.ne'
    rw [← hrank x hx]
    exact (Matrix.rank_le_card_width (1 - P x)).trans (by simp)
  obtain ⟨K₁, hK₁G, hK₁, hμ₁, hc₁⟩ := frame_pContinuous μ hP hG hμG
  obtain ⟨K₂, hK₂K₁, hK₂, hμ₂, Q, hQc, hQ⟩ :=
    frame_mColumns μ hP hK₁ hμ₁ hc₁ fun x hx => hrank x (hK₁G hx)
  obtain ⟨K₃, hK₃K₂, hK₃, hμ₃, F, hFc, hF⟩ := frame_completion μ hmd hK₂ hμ₂
    (hQc) fun x hx => (hQ x hx).1
  obtain ⟨E, hEK₃, hE, hμE, y, hyK₃, hosc⟩ := frame_smallOscillation μ hK₃ hμ₃ hFc
  obtain ⟨e, he, heE⟩ := frame_tietzeExtension hE.isClosed (hFc.mono hEK₃)
    (hF y hyK₃).1 (fun x hx => (hF x (hEK₃ hx)).1) hosc
  refine ⟨E, fun x hx => hK₁G (hK₂K₁ (hK₃K₂ (hEK₃ hx))), hE, hμE, e, he, fun x hx => ?_⟩
  have hx₃ : x ∈ K₃ := hEK₃ hx
  have hx₂ : x ∈ K₂ := hK₃K₂ hx₃
  have hxG : x ∈ G := hK₁G (hK₂K₁ hx₂)
  have hex : ∀ k : Fin d, (k : ℕ) < m → e x k = Q x k := fun k hk => by
    rw [heE x hx]; exact (hF x hx₃).2 k hk
  have himg : e x '' {k : Fin d | (k : ℕ) < m} = Q x '' {k : Fin d | (k : ℕ) < m} := by
    ext z
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, (hex k hk).symm⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, hex k hk⟩
  have hspan : Submodule.span ℝ (e x '' {k : Fin d | (k : ℕ) < m}) = vperp (V x) := by
    rw [himg]; exact (hQ x hx₂).2
  have hT := (hP.2 x).1
  have hI := (hP.2 x).2.1
  have hR := (hP.2 x).2.2
  have hsum := sum_sq_vecDot_basis_eq hT hI hR (he.2 x) hspan i
  refine ⟨fun k hk w hw => ?_, hspan, hsum, ?_⟩
  · have : e x k ∈ vperp (V x) := hspan ▸ Submodule.subset_span ⟨k, hk, rfl⟩
    exact this w hw
  · rw [hsum, ← vecEuclideanNorm_sq]
    exact pow_le_pow_left₀ hδ.le (hproj x hxG) 2

end AFree.Rademacher
