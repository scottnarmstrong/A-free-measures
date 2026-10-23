module

public import AFree.Rademacher.FrameSteps2
public import AFree.Rademacher.X0
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The continuous frame: step 5 (Tietze extension)

Step 5 of the construction of the continuous frame.
-/

@[expose] public section

open PDE MeasureTheory Filter Topology Matrix

namespace AFree.Rademacher

variable {d : ℕ}

/-- A small entrywise perturbation of an orthonormal `d`-tuple is linearly independent: if
`|G_{k,b}| ≤ 1/(4d)` then `u_k + G_k` are independent (the Frobenius norm of `G` is at most `1/4`). -/
theorem linearIndependent_add_small {u G : Fin d → Vec d}
    (hu : ∀ k l, vecDot (u k) (u l) = if k = l then 1 else 0)
    (hG : ∀ k b, |G k b| ≤ 1 / (4 * d)) : LinearIndependent ℝ (fun k => u k + G k) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k₀
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Fin.pos k₀
  set C := ∑ k, c k ^ 2 with hC
  set s : Vec d := ∑ k, c k • u k with hs
  set t : Vec d := ∑ k, c k • G k with ht
  have hst : s + t = 0 := by
    rw [hs, ht, ← Finset.sum_add_distrib]
    rw [← hc]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_add]
  have hs2 : vecNormSq s = C := by
    show vecDot s s = C
    simp only [hs, vecDot_sum_left, vecDot_sum_right, vecDot_smul_left, vecDot_smul_right, hu]
    rw [hC]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [pow_two]
  have habs : ∀ b, |t b| ≤ 1 / (4 * d) * ∑ k, |c k| := by
    intro b
    simp only [ht, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc |∑ k, c k * G k b| ≤ ∑ k, |c k * G k b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |c k| * (1 / (4 * d)) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hG k b) (abs_nonneg _)
      _ = 1 / (4 * d) * ∑ k, |c k| := by rw [← Finset.sum_mul, mul_comm]
  have hcs : (∑ k, |c k|) ^ 2 ≤ d * C := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => |c k|)
    simpa [hC, sq_abs, Finset.card_univ] using this
  have ht2 : vecNormSq t ≤ C / 16 := by
    rw [vecNormSq_eq_sum_sq]
    have hb : ∀ b, t b ^ 2 ≤ (1 / (4 * d)) ^ 2 * (d * C) := fun b => by
      have h1 := habs b
      have h2 : t b ^ 2 ≤ (1 / (4 * d) * ∑ k, |c k|) ^ 2 := by
        rw [← sq_abs (t b)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc t b ^ 2 ≤ (1 / (4 * d) * ∑ k, |c k|) ^ 2 := h2
        _ = (1 / (4 * d)) ^ 2 * (∑ k, |c k|) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcs (by positivity)
    calc ∑ b, t b ^ 2 ≤ ∑ _b : Fin d, (1 / (4 * d)) ^ 2 * (d * C) := Finset.sum_le_sum fun b _ => hb b
      _ = C / 16 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
          ring
  have hts : t = -s := by
    have := hst; rw [add_eq_zero_iff_eq_neg'] at this; exact this
  have hnorm : vecNormSq s = vecNormSq t := by
    rw [hts]
    show vecDot s s = vecDot (-s) (-s)
    simp [vecDot_eq_dotProduct]
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hCle : C ≤ 0 := by linarith
  have : c k₀ ^ 2 ≤ C := Finset.single_le_sum (f := fun k => c k ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ k₀)
  have : c k₀ ^ 2 = 0 := le_antisymm (this.trans hCle) (sq_nonneg _)
  exact pow_eq_zero_iff (two_ne_zero) |>.1 this

/-- Step 5: let `F` be continuous on a closed set `E` with values
orthonormal `d`-tuples, `y` with `F y` orthonormal and `|F(x)_{ab} - F(y)_{ab}| ≤ 1/(4d)` on `E`.
Then there is a frame `e` on `ℝ^d` with `e = F` on `E`: extend `F - F(y)` entrywise by Tietze with
values in `[-1/(4d), 1/(4d)]`, then Gram--Schmidt of the columns of `M = F(y) + G̃`. -/
theorem frame_tietzeExtension {E : Set (Vec d)} (hE : IsClosed E) {F : Vec d → Fin d → Vec d}
    (hFc : ContinuousOn F E) {y : Vec d}
    (hFy : ∀ k l, vecDot (F y k) (F y l) = if k = l then 1 else 0)
    (hFo : ∀ x ∈ E, ∀ k l, vecDot (F x k) (F x l) = if k = l then 1 else 0)
    (hosc : ∀ x ∈ E, ∀ k b : Fin d, |F x k b - F y k b| ≤ 1 / (4 * d)) :
    ∃ e : Vec d → Fin d → Vec d, IsFrame e ∧ ∀ x ∈ E, e x = F x := by
  have hB : (0 : ℝ) ≤ 1 / (4 * d) := by positivity
  have hent : ∀ k b : Fin d, ContinuousOn (fun x => F x k b - F y k b) E := fun k b =>
    (((continuous_apply b).comp_continuousOn ((continuous_apply k).comp_continuousOn hFc))).sub
      continuousOn_const
  have hex : ∀ k b : Fin d, ∃ g : C(Vec d, ℝ), (∀ x, g x ∈ Set.Icc (-(1 / (4 * (d : ℝ)))) (1 / (4 * d))) ∧
      ∀ x ∈ E, g x = F x k b - F y k b := by
    intro k b
    let f : C(E, ℝ) := ⟨fun x => F x.1 k b - F y k b, (hent k b).domRestrict⟩
    obtain ⟨g, hg1, hg2⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed f
      (t := Set.Icc (-(1 / (4 * (d : ℝ)))) (1 / (4 * d)))
      (fun x => abs_le.1 (hosc x.1 x.2 k b)) ⟨0, by constructor <;> linarith⟩ hE
    refine ⟨g, hg1, fun x hx => ?_⟩
    have h := congrArg (fun h : C(E, ℝ) => h ⟨x, hx⟩) hg2
    exact h
  choose g hgmem hgE using hex
  let M : Vec d → Fin d → Vec d := fun x k b => F y k b + g k b x
  have hMG : ∀ x, ∀ k, M x k = F y k + fun b => g k b x := fun x k => rfl
  have hMind : ∀ x, LinearIndependent ℝ (M x) := by
    intro x
    have := linearIndependent_add_small (u := F y) (G := fun k b => g k b x) hFy
      fun k b => abs_le.2 (by simpa using hgmem k b x)
    exact this
  let seqM : Vec d → ℕ → Vec d := fun x n => if h : n < d then M x ⟨n, h⟩ else 0
  have hMc : Continuous M := by
    refine continuous_pi fun k => continuous_pi fun b => ?_
    exact continuous_const.add (g k b).continuous
  have hseqc : Continuous seqM := by
    refine continuous_pi fun n => ?_
    by_cases h : n < d
    · have hc : Continuous fun x => M x ⟨n, h⟩ := (continuous_apply _).comp hMc
      simpa [seqM, h] using hc
    · simp [seqM, h]; exact continuous_const
  have hseqLI : ∀ x, LinearIndependent ℝ (fun k : Fin d => seqM x k) := fun x => by
    have : (fun k : Fin d => seqM x k) = M x := by funext k; simp [seqM, k.2]
    rw [this]; exact hMind x
  have hgs := (gram_schmidt (d := d) d).2.1
  have hcomp : ContinuousOn (fun x => fun k : Fin d => gsB (seqM x) k) Set.univ :=
    hgs.comp hseqc.continuousOn fun x _ => hseqLI x
  refine ⟨fun x k => gsB (seqM x) k, ⟨?_, fun x k l => ?_⟩, fun x hx => ?_⟩
  · exact continuousOn_univ.1 hcomp
  · have := gsB_orthonormal (hseqLI x) k.2 l.2
    simpa [Fin.ext_iff] using this
  · have hMx : ∀ k, M x k = F x k := by
      intro k; funext b
      have := hgE k b x hx
      simp only [M]; linarith
    have horth : ∀ k < d, ∀ l < d, vecDot (seqM x k) (seqM x l) = if k = l then 1 else 0 := by
      intro k hk l hl
      have := hFo x hx ⟨k, hk⟩ ⟨l, hl⟩
      simpa [seqM, hk, hl, hMx, Fin.ext_iff] using this
    funext k
    show gsB (seqM x) k = F x k
    rw [gsB_eq_self horth k k.2]
    simp [seqM, k.2, hMx]

end AFree.Rademacher
