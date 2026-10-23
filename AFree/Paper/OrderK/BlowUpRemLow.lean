module

public import AFree.Paper.OrderK.BlowUpRemainder

/-!
# The remainder is a `LowRep`

Each of the five groups of terms of `remainder_eq` is a lower-order divergence-form term with a bound
linear in the sizes `N` of the data.
-/

@[expose] public section

open MeasureTheory PDE Matrix

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The hypotheses of the cut-off system at one index `j`: the cut-off `χ`, the smooth data
`u, V, μ, Y`, the relation `μ = u P₀ + V`, the mollified equation on `B_{7/8}` and the size
bounds on `B_{7/8}` (all by a common `N`). -/
structure SystemInput (k : ℕ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (P0 : ι → ℝ) (r : ℝ)
    (χ u : Vec d → ℝ) (V μ : Vec d → ι → ℝ) (Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ)
    (N : ℝ) : Prop where
  hχ : ContDiff ℝ (⊤ : ℕ∞) χ
  hχc : HasCompactSupport χ
  hχs : tsupport χ ⊆ euclideanBall (0 : Vec d) (3 / 4)
  hu : ContDiff ℝ (⊤ : ℕ∞) u
  hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => V x i)
  hμs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => μ x i)
  hY : ∀ α β c, ContDiff ℝ (⊤ : ℕ∞) (fun x => Y α β x c)
  hμ : ∀ x, μ x = u x • P0 + V x
  hmoll : ∀ x ∈ euclideanBall (0 : Vec d) (7 / 8), ∀ c : κ,
    ∑ h ∈ Finset.range (k + 1), r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        ∑ i, Abar α c i * multiCoordDeriv α (fun y => μ y i) x =
      -(∑ h ∈ Finset.range (k + 1), r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        ∑ β ∈ multiLE α, mollSign α β * multiCoordDeriv β (fun y => Y α β y c) x)
  hNu : ∫ x in euclideanBall (0 : Vec d) (7 / 8), |u x| ≤ N
  hNV : ∀ i, ∫ x in euclideanBall (0 : Vec d) (7 / 8), |V x i| ≤ N
  hNμ : ∀ i, ∫ x in euclideanBall (0 : Vec d) (7 / 8), |μ x i| ≤ N
  hNY : ∀ α, multiAbs α ≤ k → ∀ β ∈ multiLE α, ∀ c,
    ∫ x in euclideanBall (0 : Vec d) (7 / 8), |Y α β x c| ≤ N

theorem multiAbs_iter_le {α β δ : Fin d → ℕ} (hβ : ∀ i, β i ≤ α i) (hδ : ∀ i, δ i ≤ β i) :
    multiAbs ((β - δ) + (α - β)) ≤ multiAbs α :=
  multiAbs_le_of_le fun i => by have := hβ i; have := hδ i; simp; omega

/-- The explicit constants of the five groups of terms. -/
def remKD (k : ℕ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (P0 : ι → ℝ) (c : κ) (M : ℝ) : ℝ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ β ∈ (multiLE α).erase α,
    |(Abar α *ᵥ P0) c * multiChoose α β| * cutK M β

def remKB (k : ℕ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (c : κ) (M : ℝ) : ℝ :=
  ∑ h ∈ Finset.range k, ∑ α ∈ Finset.Nat.antidiagonalTuple d h, ∑ i, |Abar α c i| * cutK M α

def remKC1 (k : ℕ) (M : ℝ) : ℝ :=
  ∑ h ∈ Finset.range k, ∑ α ∈ Finset.Nat.antidiagonalTuple d h, ∑ β ∈ multiLE α,
    |mollSign α β| * cutK M β

def remKC2 (k : ℕ) (M : ℝ) : ℝ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ β ∈ (multiLE α).erase α, |mollSign α β| * cutK M β

def remKTop (k : ℕ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (c : κ) (M : ℝ) : ℝ :=
  (∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, |Abar α c i| * cutK M α) +
    ∑ α ∈ Finset.Nat.antidiagonalTuple d k, cutK M α

/-- The total constant of the remainder, independent of the index `j`. -/
def remK (k : ℕ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (P0 : ι → ℝ) (c : κ) (M : ℝ) : ℝ :=
  remKD k Abar P0 c M + remKB k Abar c M + remKC1 (d := d) k M + remKC2 (d := d) k M +
    remKTop k Abar c M

omit [Fintype κ] in
theorem remainder_lowRep {k : ℕ} {Abar : (Fin d → ℕ) → Matrix κ ι ℝ} {P0 : ι → ℝ} {r : ℝ}
    {χ u : Vec d → ℝ} {V μ : Vec d → ι → ℝ}
    {Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ} {N M : ℝ}
    (h : SystemInput k Abar P0 r χ u V μ Y N) (hr : |r| ≤ 1) (hN0 : 0 ≤ N)
    (hM : ∀ θ : Fin d → ℕ, multiAbs θ ≤ k → ∀ x, |multiCoordDeriv θ χ x| ≤ M) (c : κ) :
    LowRepB χ k (euclideanBall (0 : Vec d) (7 / 8))
      (fun x => ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (Abar α *ᵥ P0) c *
          multiCoordDeriv α (fun y => χ y * u y) x -
        ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
          multiCoordDeriv α (fun y => systemG χ Abar V Y α y c) x) N (remK k Abar P0 c M) := by
  set S : Set (Vec d) := euclideanBall (0 : Vec d) (7 / 8) with hSdef
  have hS : tsupport χ ⊆ S := h.hχs.trans (euclideanBall_mono (by norm_num) (by norm_num))
  have hSm : MeasurableSet S := measurableSet_euclideanBall _ _
  have hint : ∀ z : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) z → IntegrableOn z S volume := fun z hz =>
    integrableOn_euclideanBall_of_continuous hz.continuous (by norm_num) (by norm_num)
  have hχs' : SmOn Set.univ χ := smOn_univ_iff.2 h.hχ
  have hder : ∀ ν, ContDiff ℝ (⊤ : ℕ∞) (multiCoordDeriv ν χ) := fun ν =>
    smOn_univ_iff.1 (hχs'.multi ν)
  have hMχ : ∀ γ : Fin d → ℕ, multiAbs γ ≤ k → ∀ δ ∈ multiLE γ, ∀ x,
      |multiCoordDeriv (γ - δ) χ x| ≤ M := fun γ hγ δ _ x =>
    hM _ ((multiAbs_sub_le γ δ).trans hγ) x
  have hmem : ∀ {α : Fin d → ℕ} {h' : ℕ}, α ∈ Finset.Nat.antidiagonalTuple d h' →
      multiAbs α = h' := fun {α h'} hα => by
    rw [Finset.Nat.mem_antidiagonalTuple] at hα; exact hα
  have hrpow : ∀ n : ℕ, |r ^ n| ≤ 1 := fun n => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg r) hr
  -- `remPD`
  have pD : LowRepB χ k S (remPD k Abar P0 c χ u) N (remKD k Abar P0 c M) := by
    refine LowRepB.sum _ fun α hα => LowRepB.sum _ fun β hβ => ?_
    have hβα : β ∈ multiLE α := Finset.mem_of_mem_erase hβ
    have hlt : multiAbs β < k := by
      rw [← hmem hα]
      exact multiAbs_lt_of_lt (mem_multiLE.1 hβα) (Finset.ne_of_mem_erase hβ)
    refine LowRepB.smul _ _ hN0 le_rfl (LowRepB.of_cut (hder _) h.hu h.hχc
      (tsupport_multiCoordDeriv_subset χ _) hS hSm (hint _ h.hu) (M := M) ?_ hlt h.hNu)
    intro δ hδ x
    have e := multiCoordDeriv_multiCoordDeriv isOpen_univ hχs' (β - δ) (α - β) (Set.mem_univ x)
    rw [e]
    exact hM _ ((multiAbs_iter_le (mem_multiLE.1 hβα) (mem_multiLE.1 hδ)).trans
      (hmem hα).le) x
  -- `remPB`
  have pB : LowRepB χ k S (remPB k Abar r c χ μ) N (remKB k Abar c M) := by
    refine LowRepB.neg hN0 (LowRepB.sum _ fun h' hh => LowRepB.sum _ fun α hα =>
      LowRepB.sum _ fun i _ => LowRepB.smul _ _ hN0 ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hrpow _)
    · have hlt : multiAbs α < k := by
        rw [hmem hα]; exact Finset.mem_range.1 hh
      exact LowRepB.of_cut h.hχ (h.hμs i) h.hχc subset_rfl hS hSm (hint _ (h.hμs i))
        (hMχ α hlt.le) hlt (h.hNμ i)
  -- `remPC1`, lower orders
  have pC1 : LowRepB χ k S (remPC1 k r c χ Y) N (remKC1 (d := d) k M) := by
    refine LowRepB.neg hN0 (LowRepB.sum _ fun h' hh => LowRepB.sum _ fun α hα =>
      LowRepB.sum _ fun β hβ => LowRepB.smul _ _ hN0 ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hrpow _)
    · have hlt : multiAbs β < k := by
        refine lt_of_le_of_lt (multiAbs_le_of_le (mem_multiLE.1 hβ)) ?_
        rw [hmem hα]; exact Finset.mem_range.1 hh
      have hαk : multiAbs α ≤ k := by
        rw [hmem hα]; exact (Finset.mem_range.1 hh).le
      exact LowRepB.of_cut h.hχ (h.hY α β c) h.hχc subset_rfl hS hSm (hint _ (h.hY α β c))
        (hMχ β hlt.le) hlt (h.hNY α hαk β hβ c)
  -- `remPC2`, order `k`, `β < α`
  have pC2 : LowRepB χ k S (remPC2 k c χ Y) N (remKC2 (d := d) k M) := by
    refine LowRepB.neg hN0 (LowRepB.sum _ fun α hα => LowRepB.sum _ fun β hβ =>
      LowRepB.smul _ _ hN0 le_rfl ?_)
    have hlt : multiAbs β < k := by
      rw [← hmem hα]
      exact multiAbs_lt_of_lt (mem_multiLE.1 (Finset.mem_of_mem_erase hβ))
        (Finset.ne_of_mem_erase hβ)
    exact LowRepB.of_cut h.hχ (h.hY α β c) h.hχc subset_rfl hS hSm (hint _ (h.hY α β c))
      (hMχ β hlt.le) hlt (h.hNY α (hmem hα).le β (Finset.mem_of_mem_erase hβ) c)
  -- `remPTop`, top order
  have pTop : LowRepB χ k S (remPTop k Abar c χ V Y) N (remKTop k Abar c M) := by
    have pA : LowRepB χ k S (fun x => ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
        (χ x * multiCoordDeriv α (fun y => V y i) x -
          multiCoordDeriv α (fun y => χ y * V y i) x)) N
        (∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, |Abar α c i| * cutK M α) := by
      refine LowRepB.sum _ fun α hα => LowRepB.sum _ fun i _ => LowRepB.smul _ _ hN0 le_rfl ?_
      exact LowRepB.of_cut_top h.hχ (h.hV i) h.hχc subset_rfl hS hSm (hint _ (h.hV i))
        (hMχ α (hmem hα).le) (hmem hα) (h.hNV i)
    have pY : LowRepB χ k S (fun x => ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
        (χ x * multiCoordDeriv α (fun y => Y α α y c) x -
          multiCoordDeriv α (fun y => χ y * Y α α y c) x)) N
        (∑ α ∈ Finset.Nat.antidiagonalTuple d k, cutK M α) := by
      refine LowRepB.sum _ fun α hα => ?_
      exact LowRepB.of_cut_top h.hχ (h.hY α α c) h.hχc subset_rfl hS hSm (hint _ (h.hY α α c))
        (hMχ α (hmem hα).le) (hmem hα)
        (h.hNY α (hmem hα).le α (mem_multiLE.2 fun i => le_rfl) c)
    exact (pA.neg hN0 |>.add (pY.neg hN0)).congr fun x _ => by simp only [remPTop]; ring
  refine ((((pD.add pB).add pC1).add pC2).add pTop).congr fun x hx => ?_
  exact (remainder_eq Abar P0 r h.hχ h.hu h.hV h.hY h.hμ c x (h.hmoll x hx c)).symm

end

end AFree
