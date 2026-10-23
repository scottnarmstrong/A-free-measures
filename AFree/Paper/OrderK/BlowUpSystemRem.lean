module

public import AFree.Paper.OrderK.BlowUpSystemAlg
public import AFree.Paper.Elliptic.Mollified

/-!
# The remainder of the cut-off system is lower order

`R = Σ_{|α|=k} a_α ∂^α(χ u) - Σ_{|α|=k} ∂^α G^{(α)}` is a lower-order divergence-form expression
on `B_{7/8}`, with a bound linear in the sizes of the data (the five groups of terms of `remainder_eq`).
-/

@[expose] public section

open MeasureTheory PDE Matrix

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `LowRep` with budget `K * N`, `K ≥ 0` explicit and independent of the data. -/
def LowRepB (χ : Vec d → ℝ) (k : ℕ) (U : Set (Vec d)) (F : Vec d → ℝ) (N K : ℝ) : Prop :=
  0 ≤ K ∧ LowRep χ k U F (K * N)

variable {χ : Vec d → ℝ} {k : ℕ} {U : Set (Vec d)} {F F' : Vec d → ℝ} {N K K' : ℝ}

theorem LowRepB.zero : LowRepB χ k U (fun _ => 0) N 0 := ⟨le_rfl, by simpa using LowRep.zero⟩

theorem LowRepB.congr (h : LowRepB χ k U F N K) (hFG : ∀ x ∈ U, F x = F' x) :
    LowRepB χ k U F' N K := ⟨h.1, h.2.congr hFG⟩

theorem LowRepB.add (h : LowRepB χ k U F N K) (h' : LowRepB χ k U F' N K') :
    LowRepB χ k U (fun x => F x + F' x) N (K + K') :=
  ⟨add_nonneg h.1 h'.1, by simpa [add_mul] using h.2.add h'.2⟩

theorem LowRepB.smul (a A : ℝ) (hN : 0 ≤ N) (ha : |a| ≤ A) (h : LowRepB χ k U F N K) :
    LowRepB χ k U (fun x => a * F x) N (A * K) := by
  refine ⟨mul_nonneg ((abs_nonneg a).trans ha) h.1, (h.2.smul a).mono ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right ha (mul_nonneg h.1 hN)

theorem LowRepB.neg (hN : 0 ≤ N) (h : LowRepB χ k U F N K) :
    LowRepB χ k U (fun x => -F x) N K := by
  have := h.smul (-1) 1 hN (by simp)
  simpa using this

theorem LowRepB.sum {ι' : Type*} (s : Finset ι') {F : ι' → Vec d → ℝ} {K : ι' → ℝ}
    (h : ∀ i ∈ s, LowRepB χ k U (F i) N (K i)) :
    LowRepB χ k U (fun x => ∑ i ∈ s, F i x) N (∑ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LowRepB.zero (χ := χ) (k := k) (U := U) (N := N))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The constant of a cut-off term. -/
def cutK (M : ℝ) (γ : Fin d → ℕ) : ℝ := M * ∑ δ ∈ multiLE γ, multiChoose γ δ

theorem LowRepB.of_cut {g z : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hz : ContDiff ℝ (⊤ : ℕ∞) z) (hcs : HasCompactSupport χ) (hgs : tsupport g ⊆ tsupport χ)
    {S : Set (Vec d)} (hS : tsupport χ ⊆ S) (hSm : MeasurableSet S)
    (hzS : IntegrableOn z S volume) {M : ℝ} {γ : Fin d → ℕ}
    (hM : ∀ δ ∈ multiLE γ, ∀ x, |multiCoordDeriv (γ - δ) g x| ≤ M) (hγ : multiAbs γ < k)
    (hN : ∫ x in S, |z x| ≤ N) :
    LowRepB χ k U (fun x => g x * multiCoordDeriv γ z x) N (cutK M γ) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM γ (mem_multiLE.2 fun i => le_rfl) 0)
  have hK : 0 ≤ cutK M γ :=
    mul_nonneg hM0 (Finset.sum_nonneg fun δ _ => multiChoose_nonneg _ _)
  refine ⟨hK, (LowRep.of_cut hg hz hcs hgs hS hSm hzS hM hγ).mono ?_⟩
  exact mul_le_mul_of_nonneg_left hN hK

theorem LowRepB.of_cut_top {g z : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hz : ContDiff ℝ (⊤ : ℕ∞) z) (hcs : HasCompactSupport χ) (hgs : tsupport g ⊆ tsupport χ)
    {S : Set (Vec d)} (hS : tsupport χ ⊆ S) (hSm : MeasurableSet S)
    (hzS : IntegrableOn z S volume) {M : ℝ} {γ : Fin d → ℕ}
    (hM : ∀ δ ∈ multiLE γ, ∀ x, |multiCoordDeriv (γ - δ) g x| ≤ M) (hγ : multiAbs γ = k)
    (hN : ∫ x in S, |z x| ≤ N) :
    LowRepB χ k U (fun x => g x * multiCoordDeriv γ z x -
      multiCoordDeriv γ (fun y => g y * z y) x) N (cutK M γ) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM γ (mem_multiLE.2 fun i => le_rfl) 0)
  have hK : 0 ≤ cutK M γ :=
    mul_nonneg hM0 (Finset.sum_nonneg fun δ _ => multiChoose_nonneg _ _)
  refine ⟨hK, (LowRep.of_cut_top hg hz hcs hgs hS hSm hzS hM hγ).mono ?_⟩
  exact mul_le_mul_of_nonneg_left hN hK

end

end AFree
