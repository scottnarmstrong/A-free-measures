module

public import AFree.Paper.OrderK.BlowUpSystemRem

/-!
# The remainder identity for the cut-off system

On `B_{7/8}`, `R = PD + PB + PC1 + PC2 + PTop`, the five groups of terms `remPD`, `remPB`, `remPC1`, `remPC2`, `remPTop`.
-/

@[expose] public section

open MeasureTheory PDE Matrix

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The terms `remPD`: the Leibniz commutators of `∂^α(χ u)`. -/
def remPD (k : ℕ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (P0 : ι → ℝ) (c : κ) (χ u : Vec d → ℝ) :
    Vec d → ℝ := fun x =>
  ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ β ∈ (multiLE α).erase α,
    ((Abar α *ᵥ P0) c * multiChoose α β) *
      (multiCoordDeriv (α - β) χ x * multiCoordDeriv β u x)

/-- The terms `remPB`: the lower-order `μ` terms. -/
def remPB (k : ℕ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (r : ℝ) (c : κ) (χ : Vec d → ℝ)
    (μ : Vec d → ι → ℝ) : Vec d → ℝ := fun x =>
  -(∑ h ∈ Finset.range k, ∑ α ∈ Finset.Nat.antidiagonalTuple d h, ∑ i,
    (r ^ (k - h) * Abar α c i) * (χ x * multiCoordDeriv α (fun y => μ y i) x))

/-- The terms `remPC1`: coefficient errors of order `h < k`. -/
def remPC1 (k : ℕ) (r : ℝ) (c : κ) (χ : Vec d → ℝ)
    (Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ) : Vec d → ℝ := fun x =>
  -(∑ h ∈ Finset.range k, ∑ α ∈ Finset.Nat.antidiagonalTuple d h, ∑ β ∈ multiLE α,
    (r ^ (k - h) * mollSign α β) * (χ x * multiCoordDeriv β (fun y => Y α β y c) x))

/-- The terms `remPC2`: order `k`, `β < α`. -/
def remPC2 (k : ℕ) (c : κ) (χ : Vec d → ℝ)
    (Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ) : Vec d → ℝ := fun x =>
  -(∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ β ∈ (multiLE α).erase α,
    mollSign α β * (χ x * multiCoordDeriv β (fun y => Y α β y c) x))

/-- The top-order commutators `χ ∂^α z - ∂^α(χ z)` appearing in the remainder. -/
def remPTop (k : ℕ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (c : κ) (χ : Vec d → ℝ)
    (V : Vec d → ι → ℝ) (Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ) : Vec d → ℝ := fun x =>
  -(∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
    (χ x * multiCoordDeriv α (fun y => V y i) x - multiCoordDeriv α (fun y => χ y * V y i) x)) -
  ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
    (χ x * multiCoordDeriv α (fun y => Y α α y c) x -
      multiCoordDeriv α (fun y => χ y * Y α α y c) x)

omit [Fintype κ] in
theorem remainder_eq {k : ℕ} (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (P0 : ι → ℝ) (r : ℝ)
    {χ u : Vec d → ℝ} {V μ : Vec d → ι → ℝ} {Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => V x i))
    (hY : ∀ α β c, ContDiff ℝ (⊤ : ℕ∞) (fun x => Y α β x c))
    (hμ : ∀ x, μ x = u x • P0 + V x) (c : κ) (x : Vec d)
    (hmoll : ∑ h ∈ Finset.range (k + 1), r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        ∑ i, Abar α c i * multiCoordDeriv α (fun y => μ y i) x =
      -(∑ h ∈ Finset.range (k + 1), r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        ∑ β ∈ multiLE α, mollSign α β * multiCoordDeriv β (fun y => Y α β y c) x)) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (Abar α *ᵥ P0) c *
        multiCoordDeriv α (fun y => χ y * u y) x -
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
        multiCoordDeriv α (fun y => systemG χ Abar V Y α y c) x =
    remPD k Abar P0 c χ u x + remPB k Abar r c χ μ x + remPC1 k r c χ Y x + remPC2 k c χ Y x +
      remPTop k Abar c χ V Y x := by
  have htop := topk_eq (k := k) Abar P0 r hμ hu hV c x hmoll
  set Sa := ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (Abar α *ᵥ P0) c * multiCoordDeriv α u x
    with hSa
  set SA := ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
    multiCoordDeriv α (fun y => V y i) x with hSA
  set SB := ∑ h ∈ Finset.range k, r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
    ∑ i, Abar α c i * multiCoordDeriv α (fun y => μ y i) x with hSB
  set SC := ∑ h ∈ Finset.range (k + 1), r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
    ∑ β ∈ multiLE α, mollSign α β * multiCoordDeriv β (fun y => Y α β y c) x with hSC
  -- Leibniz
  have h4 : ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (Abar α *ᵥ P0) c *
      multiCoordDeriv α (fun y => χ y * u y) x = χ x * Sa + remPD k Abar P0 c χ u x := by
    simp only [cut_leibniz hχ hu, mul_add, Finset.sum_add_distrib, remPD, hSa, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun α _ => by ring
    · refine Finset.sum_congr rfl fun α _ => ?_
      exact Finset.sum_congr rfl fun β _ => by ring
  have h5 : ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
      multiCoordDeriv α (fun y => systemG χ Abar V Y α y c) x =
      -(∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
        multiCoordDeriv α (fun y => χ y * V y i) x) -
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
        multiCoordDeriv α (fun y => χ y * Y α α y c) x := by
    simp only [deriv_systemG hχ Abar hV hY, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have h1 : χ x * SA = ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
      (χ x * multiCoordDeriv α (fun y => V y i) x) := by
    rw [hSA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : χ x * SB = ∑ h ∈ Finset.range k, ∑ α ∈ Finset.Nat.antidiagonalTuple d h, ∑ i,
      (r ^ (k - h) * Abar α c i) * (χ x * multiCoordDeriv α (fun y => μ y i) x) := by
    rw [hSB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : χ x * SC = ∑ h ∈ Finset.range k, ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
      ∑ β ∈ multiLE α, (r ^ (k - h) * mollSign α β) *
        (χ x * multiCoordDeriv β (fun y => Y α β y c) x) +
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
        χ x * multiCoordDeriv α (fun y => Y α α y c) x +
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ β ∈ (multiLE α).erase α,
        mollSign α β * (χ x * multiCoordDeriv β (fun y => Y α β y c) x) := by
    rw [hSC, Finset.sum_range_succ, mul_add, Finset.mul_sum, Nat.sub_self, pow_zero, one_mul,
      add_assoc]
    congr 1
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [← mul_assoc, mul_comm (χ x), mul_assoc, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hαm : α ∈ multiLE α := mem_multiLE.2 fun i => le_rfl
      rw [← Finset.add_sum_erase _ _ hαm, mul_add, Finset.mul_sum]
      congr 1
      · simp [mollSign, multiChoose_self, multiAbs]
      · exact Finset.sum_congr rfl fun β _ => by ring
  have hTopA : ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
      (χ x * multiCoordDeriv α (fun y => V y i) x - multiCoordDeriv α (fun y => χ y * V y i) x) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
        (χ x * multiCoordDeriv α (fun y => V y i) x) -
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
        multiCoordDeriv α (fun y => χ y * V y i) x := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hTopY : ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
      (χ x * multiCoordDeriv α (fun y => Y α α y c) x -
        multiCoordDeriv α (fun y => χ y * Y α α y c) x) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k, χ x * multiCoordDeriv α (fun y => Y α α y c) x -
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
        multiCoordDeriv α (fun y => χ y * Y α α y c) x := Finset.sum_sub_distrib _ _
  simp only [remPD, remPB, remPC1, remPC2, remPTop] at *
  rw [hTopA, hTopY, h4, h5]
  have e : χ x * Sa = -(χ x * SA) - χ x * SB - χ x * SC := by rw [htop]; ring
  linarith

theorem exists_deriv_bound {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ : Fin d → ℕ, multiAbs θ ≤ n → ∀ x, |multiCoordDeriv θ χ x| ≤ M := by
  have hb : ∀ θ : Fin d → ℕ, ∃ C : ℝ, ∀ x, |multiCoordDeriv θ χ x| ≤ C := fun θ => by
    have hcc := isCc_multiCoordDeriv (⟨hχ, hχc⟩ : IsCc χ) θ
    obtain ⟨C, hC⟩ := hcc.1.continuous.bounded_above_of_compact_support hcc.2
    exact ⟨C, fun x => by simpa using hC x⟩
  choose C hC using hb
  refine ⟨∑ θ ∈ lowIdx d (n + 1), |C θ|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun θ hθ x => ?_⟩
  have hmem : θ ∈ lowIdx d (n + 1) := mem_lowIdx.2 (by omega)
  exact (hC θ x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun θ => |C θ|) (fun _ _ => abs_nonneg _) hmem))

theorem multiAbs_sub_le (α δ : Fin d → ℕ) : multiAbs (α - δ) ≤ multiAbs α :=
  multiAbs_le_of_le fun i => by simp

end

end AFree
