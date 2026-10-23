module

public import AFree.Paper.OrderK.AlgebraLinear

/-!
# Lower-order divergence-form representations

`LowRep χ k U F B` says that `F = Σ_{|β|<k} ∂^β H_β` on `U`, with `H_β` smooth, compactly supported
inside `tsupport χ`, and `Σ_β ‖H_β‖_{L¹} ≤ B`. This is the bookkeeping for the cut-off system: the terms
`g ∂^γ z` with `|γ| < k` are of this form by the reverse Leibniz rule.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The multi-indices `β` with `|β| < k`. -/
def lowIdx (d k : ℕ) : Finset (Fin d → ℕ) :=
  (Finset.range k).biUnion fun h => Finset.Nat.antidiagonalTuple d h

theorem mem_lowIdx {k : ℕ} {β : Fin d → ℕ} : β ∈ lowIdx d k ↔ multiAbs β < k := by
  simp [lowIdx, Finset.mem_biUnion, Finset.Nat.mem_antidiagonalTuple, multiAbs]

theorem sum_lowIdx {M : Type*} [AddCommMonoid M] (k : ℕ) (f : (Fin d → ℕ) → M) :
    ∑ β ∈ lowIdx d k, f β = ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h, f β := by
  unfold lowIdx
  rw [Finset.sum_biUnion]
  intro h _ h' _ hne
  refine Finset.disjoint_left.2 fun β hβ hβ' => hne ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hβ hβ'
  omega

theorem multiAbs_lt_of_lt {δ γ : Fin d → ℕ} (hδ : ∀ i, δ i ≤ γ i) (hne : δ ≠ γ) :
    multiAbs δ < multiAbs γ := by
  unfold multiAbs
  refine Finset.sum_lt_sum (fun i _ => hδ i) ?_
  by_contra h
  push Not at h
  exact hne (funext fun i => le_antisymm (hδ i) (h i (Finset.mem_univ i)))

theorem multiAbs_le_of_le {δ γ : Fin d → ℕ} (hδ : ∀ i, δ i ≤ γ i) : multiAbs δ ≤ multiAbs γ :=
  Finset.sum_le_sum fun i _ => hδ i

/-- `F = Σ_{|β|<k} ∂^β H_β` on `U`, with `H_β ∈ C_c^∞`, `tsupport H_β ⊆ tsupport χ`,
`Σ_β ∫ |H_β| ≤ B`. -/
def LowRep (χ : Vec d → ℝ) (k : ℕ) (U : Set (Vec d)) (F : Vec d → ℝ) (B : ℝ) : Prop :=
  ∃ H : (Fin d → ℕ) → Vec d → ℝ, (∀ β, ContDiff ℝ (⊤ : ℕ∞) (H β)) ∧
    (∀ β, HasCompactSupport (H β)) ∧ (∀ β, tsupport (H β) ⊆ tsupport χ) ∧
    (∀ x ∈ U, F x = ∑ β ∈ lowIdx d k, multiCoordDeriv β (H β) x) ∧
    ∑ β ∈ lowIdx d k, ∫ x, |H β x| ≤ B

variable {χ : Vec d → ℝ} {k : ℕ} {U : Set (Vec d)} {F F' : Vec d → ℝ} {B B' : ℝ}

theorem LowRep.zero : LowRep χ k U (fun _ => 0) 0 :=
  ⟨fun _ _ => 0, fun _ => contDiff_const, fun _ => HasCompactSupport.zero,
    fun β => by simp, fun x _ => by simp [multiCoordDeriv_zero_fun], by simp⟩

theorem LowRep.mono (h : LowRep χ k U F B) (hB : B ≤ B') : LowRep χ k U F B' := by
  obtain ⟨H, h1, h2, h3, h4, h5⟩ := h
  exact ⟨H, h1, h2, h3, h4, h5.trans hB⟩

theorem LowRep.congr (h : LowRep χ k U F B) (hFG : ∀ x ∈ U, F x = F' x) : LowRep χ k U F' B := by
  obtain ⟨H, h1, h2, h3, h4, h5⟩ := h
  exact ⟨H, h1, h2, h3, fun x hx => (hFG x hx).symm.trans (h4 x hx), h5⟩

theorem LowRep.add (h : LowRep χ k U F B) (h' : LowRep χ k U F' B') :
    LowRep χ k U (fun x => F x + F' x) (B + B') := by
  obtain ⟨H, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨H', h1', h2', h3', h4', h5'⟩ := h'
  refine ⟨fun β x => H β x + H' β x, fun β => (h1 β).add (h1' β),
    fun β => (h2 β).add (h2' β), fun β => ?_, fun x hx => ?_, ?_⟩
  · exact (tsupport_add (H β) (H' β)).trans (Set.union_subset (h3 β) (h3' β))
  · simp only [multiCoordDeriv_add_global (h1 _) (h1' _), Finset.sum_add_distrib]
    rw [h4 x hx, h4' x hx]
  · have hi : ∀ β, Integrable (H β) := fun β => (h1 β).continuous.integrable_of_hasCompactSupport (h2 β)
    have hi' : ∀ β, Integrable (H' β) := fun β =>
      (h1' β).continuous.integrable_of_hasCompactSupport (h2' β)
    calc ∑ β ∈ lowIdx d k, ∫ x, |H β x + H' β x|
        ≤ ∑ β ∈ lowIdx d k, ((∫ x, |H β x|) + ∫ x, |H' β x|) := by
          refine Finset.sum_le_sum fun β _ => ?_
          rw [← integral_add (hi β).abs (hi' β).abs]
          exact integral_mono ((hi β).add (hi' β)).abs ((hi β).abs.add (hi' β).abs)
            fun x => abs_add_le _ _
      _ = _ := Finset.sum_add_distrib
      _ ≤ B + B' := add_le_add h5 h5'

theorem LowRep.smul (a : ℝ) (h : LowRep χ k U F B) :
    LowRep χ k U (fun x => a * F x) (|a| * B) := by
  obtain ⟨H, h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun β x => a * H β x, fun β => (h1 β).const_smul a, fun β => (h2 β).mul_left,
    fun β => ?_, fun x hx => ?_, ?_⟩
  · exact (tsupport_smul_subset_right (fun _ => a) (H β)).trans (h3 β)
  · beta_reduce
    rw [h4 x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [multiCoordDeriv_const_mul (h1 β) a β]
  · calc ∑ β ∈ lowIdx d k, ∫ x, |a * H β x| = ∑ β ∈ lowIdx d k, |a| * ∫ x, |H β x| := by
          refine Finset.sum_congr rfl fun β _ => ?_
          simp only [abs_mul]
          rw [integral_const_mul]
      _ = |a| * ∑ β ∈ lowIdx d k, ∫ x, |H β x| := by rw [Finset.mul_sum]
      _ ≤ |a| * B := mul_le_mul_of_nonneg_left h5 (abs_nonneg a)

/-- Any finite family of slots indexed by `T ⊆ {|β| < k}` gives a `LowRep`. -/
theorem LowRep.of_family (T : Finset (Fin d → ℕ)) (hT : ∀ β ∈ T, multiAbs β < k)
    (slot : (Fin d → ℕ) → Vec d → ℝ) (h1 : ∀ β, ContDiff ℝ (⊤ : ℕ∞) (slot β))
    (h2 : ∀ β, HasCompactSupport (slot β)) (h3 : ∀ β, tsupport (slot β) ⊆ tsupport χ) :
    LowRep χ k U (fun x => ∑ β ∈ T, multiCoordDeriv β (slot β) x) (∑ β ∈ T, ∫ x, |slot β x|) := by
  classical
  refine ⟨fun β => if β ∈ T then slot β else fun _ => 0, fun β => ?_, fun β => ?_,
    fun β => ?_, fun x _ => ?_, ?_⟩
  · by_cases hβ : β ∈ T
    · simpa [hβ] using h1 β
    · simpa [hβ] using contDiff_const
  · by_cases hβ : β ∈ T
    · simpa [hβ] using h2 β
    · simp only [hβ, ite_false]; exact HasCompactSupport.zero
  · by_cases hβ : β ∈ T
    · simpa [hβ] using h3 β
    · simp [hβ]
  · have hsub : T ⊆ lowIdx d k := fun β hβ => mem_lowIdx.2 (hT β hβ)
    have : ∑ β ∈ lowIdx d k, multiCoordDeriv β (if β ∈ T then slot β else fun _ => 0) x =
        ∑ β ∈ lowIdx d k, if β ∈ T then multiCoordDeriv β (slot β) x else 0 := by
      refine Finset.sum_congr rfl fun β _ => ?_
      by_cases hβ : β ∈ T
      · simp [hβ]
      · simp [hβ, multiCoordDeriv_zero_fun]
    rw [this, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
  · have hsub : T ⊆ lowIdx d k := fun β hβ => mem_lowIdx.2 (hT β hβ)
    have : ∑ β ∈ lowIdx d k, ∫ x, |(if β ∈ T then slot β else fun _ => (0 : ℝ)) x| =
        ∑ β ∈ lowIdx d k, if β ∈ T then ∫ x, |slot β x| else 0 := by
      refine Finset.sum_congr rfl fun β _ => ?_
      by_cases hβ : β ∈ T
      · simp [hβ]
      · simp [hβ]
    rw [this, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]

end

end AFree
