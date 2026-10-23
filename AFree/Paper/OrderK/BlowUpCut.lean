module

public import AFree.Paper.OrderK.BlowUpLow

/-!
# Cut-off terms are lower-order divergence-form terms

For `|γ| < k`, `g ∂^γ z` is in `LowRep` by the reverse Leibniz rule; for
`|γ| = k` the same holds for `g ∂^γ z - ∂^γ(g z)`.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

noncomputable section

variable {d : ℕ} {χ g z : Vec d → ℝ} {k : ℕ} {U : Set (Vec d)}

theorem multiChoose_nonneg (α β : Fin d → ℕ) : 0 ≤ multiChoose α β :=
  Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _

theorem multiChoose_self (α : Fin d → ℕ) : multiChoose α α = 1 := by simp [multiChoose]

theorem sub_self_pi (α : Fin d → ℕ) : α - α = 0 := by funext _; simp

/-- The slot of the reverse Leibniz rule. -/
def cutSlot (g z : Vec d → ℝ) (γ δ : Fin d → ℕ) : Vec d → ℝ :=
  fun x => (-1 : ℝ) ^ multiAbs (γ - δ) * multiChoose γ δ * (multiCoordDeriv (γ - δ) g x * z x)

theorem cutSlot_prop (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hz : ContDiff ℝ (⊤ : ℕ∞) z)
    (hcs : HasCompactSupport χ) (hgs : tsupport g ⊆ tsupport χ) (γ δ : Fin d → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutSlot g z γ δ) ∧ HasCompactSupport (cutSlot g z γ δ) ∧
      tsupport (cutSlot g z γ δ) ⊆ tsupport χ := by
  have hgm : ContDiff ℝ (⊤ : ℕ∞) (multiCoordDeriv (γ - δ) g) :=
    smOn_univ_iff.1 ((smOn_univ_iff.2 hg).multi _)
  have hsub : tsupport (cutSlot g z γ δ) ⊆ tsupport χ := by
    refine (tsupport_smul_subset_right (fun _ => (-1 : ℝ) ^ multiAbs (γ - δ) * multiChoose γ δ)
      (fun x => multiCoordDeriv (γ - δ) g x * z x)).trans ?_
    exact (tsupport_mul_subset_left (f := multiCoordDeriv (γ - δ) g) (g := z)).trans
      ((tsupport_multiCoordDeriv_subset g (γ - δ)).trans hgs)
  exact ⟨contDiff_const.mul (hgm.mul hz), IsCompact.of_isClosed_subset hcs (isClosed_tsupport _) hsub,
    hsub⟩

theorem cut_identity (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hz : ContDiff ℝ (⊤ : ℕ∞) z) (γ : Fin d → ℕ)
    (x : Vec d) :
    g x * multiCoordDeriv γ z x = ∑ δ ∈ multiLE γ, multiCoordDeriv δ (cutSlot g z γ δ) x := by
  rw [(lem_revleibniz hg hz γ).1 x]
  refine Finset.sum_congr rfl fun δ _ => ?_
  have hgm : ContDiff ℝ (⊤ : ℕ∞) (multiCoordDeriv (γ - δ) g) :=
    smOn_univ_iff.1 ((smOn_univ_iff.2 hg).multi _)
  unfold cutSlot
  rw [multiCoordDeriv_const_mul (hgm.mul hz) _ δ]

theorem integral_abs_cutSlot_le (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hz : ContDiff ℝ (⊤ : ℕ∞) z)
    (hcs : HasCompactSupport χ) (hgs : tsupport g ⊆ tsupport χ) {S : Set (Vec d)}
    (hS : tsupport χ ⊆ S) (hSm : MeasurableSet S) (hzS : IntegrableOn z S volume) {M : ℝ} {γ δ : Fin d → ℕ}
    (hM : ∀ x, |multiCoordDeriv (γ - δ) g x| ≤ M) :
    ∫ x, |cutSlot g z γ δ x| ≤ multiChoose γ δ * M * ∫ x in S, |z x| := by
  obtain ⟨h1, h2, h3⟩ := cutSlot_prop hg hz hcs hgs γ δ
  have hzero : ∀ x ∉ S, |cutSlot g z γ δ x| = 0 := by
    intro x hx
    have : x ∉ tsupport (cutSlot g z γ δ) := fun h => hx (hS (h3 h))
    simp [image_eq_zero_of_notMem_tsupport this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hint : IntegrableOn (fun x => |cutSlot g z γ δ x|) S volume :=
    (h1.continuous.integrable_of_hasCompactSupport h2).abs.integrableOn
  calc ∫ x in S, |cutSlot g z γ δ x|
      ≤ ∫ x in S, multiChoose γ δ * M * |z x| := by
        refine setIntegral_mono_on hint (hzS.abs.const_mul _) hSm fun x _ => ?_
        unfold cutSlot
        rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (multiChoose_nonneg γ δ)]
        have h := mul_le_mul_of_nonneg_right (hM x) (abs_nonneg (z x))
        calc multiChoose γ δ * (|multiCoordDeriv (γ - δ) g x| * |z x|)
            ≤ multiChoose γ δ * (M * |z x|) := mul_le_mul_of_nonneg_left h (multiChoose_nonneg γ δ)
          _ = _ := by ring
    _ = _ := integral_const_mul _ _

/-- A cut-off term `g ∂^γ z` with `|γ| < k` is a lower-order divergence-form term. -/
theorem LowRep.of_cut (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hz : ContDiff ℝ (⊤ : ℕ∞) z)
    (hcs : HasCompactSupport χ) (hgs : tsupport g ⊆ tsupport χ) {S : Set (Vec d)}
    (hS : tsupport χ ⊆ S) (hSm : MeasurableSet S) (hzS : IntegrableOn z S volume)
    {M : ℝ} {γ : Fin d → ℕ} (hM : ∀ δ ∈ multiLE γ, ∀ x, |multiCoordDeriv (γ - δ) g x| ≤ M)
    (hγ : multiAbs γ < k) :
    LowRep χ k U (fun x => g x * multiCoordDeriv γ z x)
      ((M * ∑ δ ∈ multiLE γ, multiChoose γ δ) * ∫ x in S, |z x|) := by
  have hT : ∀ β ∈ multiLE γ, multiAbs β < k := fun β hβ =>
    lt_of_le_of_lt (multiAbs_le_of_le (mem_multiLE.1 hβ)) hγ
  have := LowRep.of_family (U := U) (χ := χ) (multiLE γ) hT (cutSlot g z γ)
    (fun δ => (cutSlot_prop hg hz hcs hgs γ δ).1) (fun δ => (cutSlot_prop hg hz hcs hgs γ δ).2.1)
    (fun δ => (cutSlot_prop hg hz hcs hgs γ δ).2.2)
  refine (this.congr fun x _ => (cut_identity hg hz γ x).symm).mono ?_
  calc ∑ δ ∈ multiLE γ, ∫ x, |cutSlot g z γ δ x|
      ≤ ∑ δ ∈ multiLE γ, multiChoose γ δ * M * ∫ x in S, |z x| :=
        Finset.sum_le_sum fun δ hδ =>
          integral_abs_cutSlot_le hg hz hcs hgs hS hSm hzS (hM δ hδ)
    _ = _ := by rw [← Finset.sum_mul]; congr 1; rw [Finset.mul_sum]; exact
          Finset.sum_congr rfl fun δ _ => mul_comm _ _

/-- For `|γ| = k`, `g ∂^γ z - ∂^γ(g z)` is a lower-order divergence-form term. -/
theorem LowRep.of_cut_top (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hz : ContDiff ℝ (⊤ : ℕ∞) z)
    (hcs : HasCompactSupport χ) (hgs : tsupport g ⊆ tsupport χ) {S : Set (Vec d)}
    (hS : tsupport χ ⊆ S) (hSm : MeasurableSet S) (hzS : IntegrableOn z S volume)
    {M : ℝ} {γ : Fin d → ℕ} (hM : ∀ δ ∈ multiLE γ, ∀ x, |multiCoordDeriv (γ - δ) g x| ≤ M)
    (hγ : multiAbs γ = k) :
    LowRep χ k U (fun x => g x * multiCoordDeriv γ z x - multiCoordDeriv γ (fun y => g y * z y) x)
      ((M * ∑ δ ∈ multiLE γ, multiChoose γ δ) * ∫ x in S, |z x|) := by
  classical
  have hγm : γ ∈ multiLE γ := mem_multiLE.2 fun i => le_rfl
  have hT : ∀ β ∈ (multiLE γ).erase γ, multiAbs β < k := fun β hβ => by
    rw [← hγ]
    exact multiAbs_lt_of_lt (mem_multiLE.1 (Finset.mem_of_mem_erase hβ))
      (Finset.ne_of_mem_erase hβ)
  have := LowRep.of_family (U := U) (χ := χ) ((multiLE γ).erase γ) hT (cutSlot g z γ)
    (fun δ => (cutSlot_prop hg hz hcs hgs γ δ).1) (fun δ => (cutSlot_prop hg hz hcs hgs γ δ).2.1)
    (fun δ => (cutSlot_prop hg hz hcs hgs γ δ).2.2)
  refine (this.congr fun x _ => ?_).mono ?_
  · rw [cut_identity hg hz γ x, ← Finset.add_sum_erase _ _ hγm]
    have : cutSlot g z γ γ = fun y => g y * z y := by
      funext y
      simp [cutSlot, multiChoose_self, sub_self_pi, multiAbs, multiCoordDeriv_zero]
    rw [this]
    ring
  · calc ∑ δ ∈ (multiLE γ).erase γ, ∫ x, |cutSlot g z γ δ x|
        ≤ ∑ δ ∈ (multiLE γ).erase γ, multiChoose γ δ * M * ∫ x in S, |z x| :=
          Finset.sum_le_sum fun δ hδ =>
            integral_abs_cutSlot_le hg hz hcs hgs hS hSm hzS (hM δ (Finset.mem_of_mem_erase hδ))
      _ ≤ ∑ δ ∈ multiLE γ, multiChoose γ δ * M * ∫ x in S, |z x| := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun δ _ _ => ?_
          have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM δ ‹_› 0)
          exact mul_nonneg (mul_nonneg (multiChoose_nonneg _ _) hM0)
            (setIntegral_nonneg hSm fun x _ => abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; congr 1; rw [Finset.mul_sum]; exact
            Finset.sum_congr rfl fun δ _ => mul_comm _ _

end

end AFree
