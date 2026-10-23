module

public import AFree.Rademacher.Lusin
public import AFree.Rademacher.GramSchmidt
public import AFree.Rademacher.FrameAlg
public import AFree.Rademacher.FrameLemmas

/-!
# The continuous frame: steps 1 and 2

Steps 1 and 2 of the construction of the continuous frame.
-/

@[expose] public section

open PDE MeasureTheory Filter Topology Matrix

namespace AFree.Rademacher

variable {d : ℕ}

/-- Step 1: by Lusin's theorem there is a compact `K₁ ⊆ G` with
`μ K₁ > 0` on which the (Borel, bounded) projection field `P` is continuous. -/
theorem frame_pContinuous (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {V : Vec d → Submodule ℝ (Vec d)} {P : Vec d → Matrix (Fin d) (Fin d) ℝ}
    (hP : IsBorelProj V P) {G : Set (Vec d)} (hG : MeasurableSet G) (hμ : 0 < μ G) :
    ∃ K₁ ⊆ G, IsCompact K₁ ∧ 0 < μ K₁ ∧ ContinuousOn P K₁ := by
  have hmeas : Measurable fun x => (fun a b => P x a b : Fin d → Fin d → ℝ) :=
    measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => hP.1 a b
  have hbd : ∃ C : ℝ, ∀ x, ‖(fun a b => P x a b : Fin d → Fin d → ℝ)‖ ≤ C := by
    refine ⟨1, fun x => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_⟩
    rw [Real.norm_eq_abs]
    exact abs_entry_le_one (hP.2 x).1 (hP.2 x).2.1 a b
  obtain ⟨K, hKG, hK, hKμ, hKc⟩ := lusin_aux μ hG hμ hmeas hbd
  exact ⟨K, hKG, hK, hKμ, hKc⟩

theorem continuousOn_entry {K : Set (Vec d)} {P : Vec d → Matrix (Fin d) (Fin d) ℝ}
    (hc : ContinuousOn P K) (a b : Fin d) : ContinuousOn (fun x => P x a b) K :=
  (continuous_apply b).comp_continuousOn ((continuous_apply a).comp_continuousOn hc)

theorem continuousOn_col_one_sub {K : Set (Vec d)} {P : Vec d → Matrix (Fin d) (Fin d) ℝ}
    (hc : ContinuousOn P K) (a : Fin d) : ContinuousOn (fun x => (1 - P x).col a) K := by
  refine continuousOn_pi.2 fun b => ?_
  refine ContinuousOn.congr (f := fun x => (1 : Matrix (Fin d) (Fin d) ℝ) b a - P x b a)
    (continuousOn_const.sub (continuousOn_entry hc b a)) fun x _ => ?_
  simp [Matrix.col]

/-- Step 2: where `P` is continuous on a compact `K₁` of positive measure
and `rank (Id - P) = m`, there are a compact `K₂ ⊆ K₁` of positive measure and Gram--Schmidt
vectors `Q_0, …, Q_{m-1}` of `m` independent columns of `Id - P`: continuous on `K₂`, orthonormal and
spanning `V(x)^⊥`. -/
theorem frame_mColumns (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {V : Vec d → Submodule ℝ (Vec d)} {P : Vec d → Matrix (Fin d) (Fin d) ℝ}
    (hP : IsBorelProj V P) {m : ℕ} {K₁ : Set (Vec d)} (hK₁ : IsCompact K₁) (hμ : 0 < μ K₁)
    (hc : ContinuousOn P K₁) (hrank : ∀ x ∈ K₁, (1 - P x).rank = m) :
    ∃ K₂ ⊆ K₁, IsCompact K₂ ∧ 0 < μ K₂ ∧ ∃ Q : Vec d → Fin d → Vec d,
      ContinuousOn Q K₂ ∧ ∀ x ∈ K₂,
        (∀ k l : Fin d, (k : ℕ) < m → (l : ℕ) < m →
          vecDot (Q x k) (Q x l) = if k = l then 1 else 0) ∧
        Submodule.span ℝ (Q x '' {k : Fin d | (k : ℕ) < m}) = vperp (V x) := by
  obtain ⟨y, hyK, hy⟩ := exists_density_point μ hK₁ hμ
  -- `m` independent columns at `y`
  obtain ⟨κ, a, hainj, hspan, hli⟩ := exists_linearIndependent' ℝ (fun a : Fin d => (1 - P y).col a)
  have : Finite κ := Finite.of_injective a hainj
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = m := by
    have h1 := finrank_span_eq_card hli
    rw [← hrank y hyK, Matrix.rank_eq_finrank_span_cols, ← hspan]
    exact h1.symm
  have hmd : m ≤ d := by
    rw [← hcard]
    simpa using Fintype.card_le_of_injective a hainj
  let e : κ ≃ Fin m := Fintype.equivFinOfCardEq hcard
  let σ : Fin m → Fin d := a ∘ e.symm
  have hliy : LinearIndependent ℝ (fun k : Fin m => (1 - P y).col (σ k)) :=
    hli.comp e.symm e.symm.injective
  -- the family of chosen columns is continuous on `K₁` and independent near `y`
  let Φ : Vec d → Fin m → Vec d := fun x k => (1 - P x).col (σ k)
  have hΦ : ContinuousOn Φ K₁ := continuousOn_pi.2 fun k => continuousOn_col_one_sub hc (σ k)
  have hU : IsOpen {f : Fin m → Vec d | LinearIndependent ℝ f} :=
    isOpen_setOfPred_linearIndependent
  have hev := (hΦ y hyK).eventually_mem (hU.mem_nhds hliy)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεU⟩ := hev
  set K₂ := K₁ ∩ Metric.closedBall y (ε / 2) with hK₂
  have hK₂c : IsCompact K₂ := hK₁.inter_right Metric.isClosed_closedBall
  have hind : ∀ x ∈ K₂, LinearIndependent ℝ (Φ x) := fun x hx => hεU
    (lt_of_le_of_lt (Metric.mem_closedBall.1 hx.2) (by linarith)) hx.1
  refine ⟨K₂, Set.inter_subset_left, hK₂c, hy _ (by positivity), ?_⟩
  -- the Gram--Schmidt vectors
  let seq : Vec d → ℕ → Vec d := fun x n => if h : n < m then Φ x ⟨n, h⟩ else 0
  have hseqΦ : ∀ x, (fun k : Fin m => seq x k) = Φ x := by
    intro x; funext k; simp [seq, k.2]
  have hseqc : ContinuousOn (fun x => seq x) K₂ := by
    refine continuousOn_pi.2 fun n => ?_
    by_cases h : n < m
    · have := (continuousOn_pi (f := Φ)).1 (hΦ.mono (show K₂ ⊆ K₁ from Set.inter_subset_left)) ⟨n, h⟩
      simpa [seq, h] using this
    · simp [seq, h]; exact continuousOn_const
  have hgs := (gram_schmidt (d := d) m).2.1
  have hcomp : ContinuousOn (fun x => fun k : Fin m => gsB (seq x) k) K₂ :=
    hgs.comp hseqc fun x hx => by
      show LinearIndependent ℝ (fun k : Fin m => seq x k)
      rw [hseqΦ]; exact hind x hx
  let Q : Vec d → Fin d → Vec d := fun x k => if (k : ℕ) < m then gsB (seq x) k else 0
  refine ⟨Q, continuousOn_pi.2 fun k => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · by_cases h : (k : ℕ) < m
    · have := (continuousOn_pi (f := fun x => fun k : Fin m => gsB (seq x) k)).1 hcomp ⟨k, h⟩
      simpa [Q, h] using this
    · simp [Q, h]; exact continuousOn_const
  · intro k l hk hl
    have hLI : LinearIndependent ℝ (fun k : Fin m => seq x k) := by
      rw [hseqΦ]; exact hind x hx
    have := gsB_orthonormal hLI hk hl
    simpa [Q, hk, hl, Fin.ext_iff] using this
  · have hLI : LinearIndependent ℝ (fun k : Fin m => seq x k) := by
      rw [hseqΦ]; exact hind x hx
    have hxK : x ∈ K₁ := hx.1
    have hT := (hP.2 x).1
    have hI := (hP.2 x).2.1
    have hR := (hP.2 x).2.2
    -- the image set of `Q x` is the image of `gsB (seq x)` on `Iio m`
    have himg : Q x '' {k : Fin d | (k : ℕ) < m} = gsB (seq x) '' Set.Iio m := by
      ext z
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hk' : (k : ℕ) < m := hk
        exact ⟨k, hk', by simp [Q, hk']⟩
      · rintro ⟨n, hn, rfl⟩
        have hn' : n < m := hn
        exact ⟨⟨n, lt_of_lt_of_le hn' hmd⟩, hn', by simp [Q, hn']⟩
    rw [himg, span_gsB hLI le_rfl]
    have himg2 : seq x '' Set.Iio m = Set.range (Φ x) := by
      ext z
      constructor
      · rintro ⟨n, hn, rfl⟩
        have hn' : n < m := hn
        exact ⟨⟨n, hn'⟩, by simp [seq, hn']⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, k.2, by simp [seq, k.2]⟩
    rw [himg2]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact col_one_sub_mem_vperp hT hI hR (σ k)
    · rw [finrank_span_eq_card (hind x hx), Fintype.card_fin,
        ← rank_one_sub_eq_finrank hT hI hR, hrank x hxK]

end AFree.Rademacher
