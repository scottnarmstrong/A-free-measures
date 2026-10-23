module

public import AFree.Rademacher.FrameSteps1

/-!
# The continuous frame: steps 3 and 4

Steps 3 and 4 of the construction of the continuous frame.
-/

@[expose] public section

open PDE MeasureTheory Filter Topology Matrix

namespace AFree.Rademacher

variable {d : ℕ}

/-- Step 3: an orthonormal `m`-tuple `Q₀, …, Q_{m-1}`, continuous on a
compact `K₂` of positive measure, is completed on a compact `K₃ ⊆ K₂` of positive measure to a
continuous orthonormal `d`-tuple `F` (a continuous map into `O(d)`, by columns) with `F_k = Q_k`
for `k < m`. The completion vectors are standard basis vectors chosen at one density point, and
`F` is the Gram--Schmidt of `(Q₀, …, Q_{m-1}, completion)`. -/
theorem frame_completion (μ : Measure (Vec d)) [IsFiniteMeasure μ] {m : ℕ} (hm : m ≤ d)
    {K₂ : Set (Vec d)} (hK₂ : IsCompact K₂) (hμ : 0 < μ K₂) {Q : Vec d → Fin d → Vec d}
    (hQc : ContinuousOn Q K₂)
    (hQo : ∀ x ∈ K₂, ∀ k l : Fin d, (k : ℕ) < m → (l : ℕ) < m →
      vecDot (Q x k) (Q x l) = if k = l then 1 else 0) :
    ∃ K₃ ⊆ K₂, IsCompact K₃ ∧ 0 < μ K₃ ∧ ∃ F : Vec d → Fin d → Vec d,
      ContinuousOn F K₃ ∧ ∀ x ∈ K₃,
        (∀ k l : Fin d, vecDot (F x k) (F x l) = if k = l then 1 else 0) ∧
        ∀ k : Fin d, (k : ℕ) < m → F x k = Q x k := by
  obtain ⟨y, hyK, hy⟩ := exists_density_point μ hK₂ hμ
  let seq0 : Vec d → ℕ → Vec d := fun x n => if h : n < d then Q x ⟨n, h⟩ else 0
  have hQy : LinearIndependent ℝ (fun k : Fin m => seq0 y k) := by
    refine linearIndependent_of_orthonormal fun k l => ?_
    have hk : (k : ℕ) < d := lt_of_lt_of_le k.2 hm
    have hl : (l : ℕ) < d := lt_of_lt_of_le l.2 hm
    have := hQo y hyK ⟨k, hk⟩ ⟨l, hl⟩ k.2 l.2
    simpa [seq0, hk, hl, Fin.ext_iff] using this
  obtain ⟨w, hw1, hw2⟩ := exists_extend_independent hm hQy
  let wseq : Vec d → ℕ → Vec d := fun x n => if n < m then seq0 x n else w n
  have hwy : (fun k : Fin d => wseq y k) = fun k : Fin d => w k := by
    funext k
    by_cases h : (k : ℕ) < m
    · simp [wseq, h, hw1 k h]
    · simp [wseq, h]
  have hwseqc : ContinuousOn wseq K₂ := by
    refine continuousOn_pi.2 fun n => ?_
    by_cases h : n < m
    · by_cases hd : n < d
      · have := (continuousOn_pi (f := Q)).1 hQc ⟨n, hd⟩
        simpa [wseq, seq0, h, hd] using this
      · exact absurd (lt_of_lt_of_le h hm) hd
    · simp [wseq, h]; exact continuousOn_const
  have hU : IsOpen {a : ℕ → Vec d | LinearIndependent ℝ (fun k : Fin d => a k)} :=
    isOpen_linearIndependent d
  have hyU : wseq y ∈ {a : ℕ → Vec d | LinearIndependent ℝ (fun k : Fin d => a k)} := by
    show LinearIndependent ℝ (fun k : Fin d => wseq y k)
    rw [hwy]; exact hw2
  have hev := (hwseqc y hyK).eventually_mem (hU.mem_nhds hyU)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεU⟩ := hev
  set K₃ := K₂ ∩ Metric.closedBall y (ε / 2) with hK₃
  have hK₃c : IsCompact K₃ := hK₂.inter_right Metric.isClosed_closedBall
  have hind : ∀ x ∈ K₃, LinearIndependent ℝ (fun k : Fin d => wseq x k) := fun x hx => hεU
    (lt_of_le_of_lt (Metric.mem_closedBall.1 hx.2) (by linarith)) hx.1
  refine ⟨K₃, Set.inter_subset_left, hK₃c, hy _ (by positivity),
    fun x k => gsB (wseq x) k, ?_, fun x hx => ⟨?_, ?_⟩⟩
  · refine continuousOn_pi.2 fun k => ?_
    have hgs := (gram_schmidt (d := d) d).2.1
    have hcomp : ContinuousOn (fun x => fun k : Fin d => gsB (wseq x) k) K₃ :=
      hgs.comp (hwseqc.mono (show K₃ ⊆ K₂ from Set.inter_subset_left)) fun x hx => hind x hx
    exact (continuousOn_pi (f := fun x => fun k : Fin d => gsB (wseq x) k)).1 hcomp k
  · intro k l
    have := gsB_orthonormal (hind x hx) k.2 l.2
    simpa [Fin.ext_iff] using this
  · intro k hk
    have hxK : x ∈ K₂ := hx.1
    have horth : ∀ k < m, ∀ l < m, vecDot (wseq x k) (wseq x l) = if k = l then 1 else 0 := by
      intro k hk l hl
      have hkd : k < d := lt_of_lt_of_le hk hm
      have hld : l < d := lt_of_lt_of_le hl hm
      have := hQo x hxK ⟨k, hkd⟩ ⟨l, hld⟩ hk hl
      simpa [wseq, seq0, hk, hl, hkd, hld, Fin.ext_iff] using this
    have := gsB_eq_self horth k hk
    show gsB (wseq x) k = Q x k
    rw [this]
    have hkd : (k : ℕ) < d := k.2
    simp [wseq, seq0, hk, hkd]

/-- Step 4: for `F` continuous on a compact `K₃` of positive
measure there are a compact `E ⊆ K₃` of positive measure and `y ∈ K₃` with
`|F(x)_{ab} - F(y)_{ab}| ≤ 1/(4d)` for `x ∈ E` (entries: the `b`-th coordinate of the `k`-th
column). -/
theorem frame_smallOscillation (μ : Measure (Vec d)) [IsFiniteMeasure μ] {K₃ : Set (Vec d)}
    (hK₃ : IsCompact K₃) (hμ : 0 < μ K₃) {F : Vec d → Fin d → Vec d} (hFc : ContinuousOn F K₃) :
    ∃ E ⊆ K₃, IsCompact E ∧ 0 < μ E ∧ ∃ y ∈ K₃, ∀ x ∈ E, ∀ k b : Fin d,
      |F x k b - F y k b| ≤ 1 / (4 * d) := by
  obtain ⟨y, hyK, hy⟩ := exists_density_point μ hK₃ hμ
  have hε : (0 : ℝ) < 1 / (4 * d + 4) := by positivity
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousWithinAt_iff.1 (hFc y hyK) _ hε
  refine ⟨K₃ ∩ Metric.closedBall y (δ / 2), Set.inter_subset_left,
    hK₃.inter_right Metric.isClosed_closedBall, hy _ (by positivity), y, hyK, ?_⟩
  rintro x ⟨hxK, hxb⟩ k b
  have hdpos : 0 < d := Fin.pos k
  have hdist := hδF hxK (lt_of_le_of_lt (Metric.mem_closedBall.1 hxb) (by linarith))
  have h1 : |F x k b - F y k b| ≤ dist (F x) (F y) := by
    have h2 : ‖(F x k - F y k) b‖ ≤ ‖F x k - F y k‖ := norm_le_pi_norm _ b
    have h3 : ‖F x k - F y k‖ ≤ ‖F x - F y‖ := norm_le_pi_norm (F x - F y) k
    rw [dist_eq_norm]
    simpa [Real.norm_eq_abs] using h2.trans h3
  have h4 : 1 / (4 * (d : ℝ) + 4) ≤ 1 / (4 * d) := by
    have : (0 : ℝ) < d := by exact_mod_cast hdpos
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

end AFree.Rademacher
