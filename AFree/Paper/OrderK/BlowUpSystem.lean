module

public import AFree.Paper.OrderK.BlowUpRemLow
public import AFree.Measure.PolarFacts

/-!
# The cut-off system at one index

The fixed-index form of the cut-off lemma: from the mollified equation on `B_{7/8}`, the cut-off `χ u`
satisfies `Σ_{|α|=k} A_α P₀ ∂^α(χ u) = Σ ∂^α G^{(α)} + Σ_{|β|<k} ∂^β H_β` on all of `ℝ^d`, with the
explicit `G^{(α)} = -χ(Ā_α V + Y_{α,α})` and `H_β` of `L¹`-size `O(N)`.
-/

@[expose] public section

open MeasureTheory PDE Matrix

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem multiCoordDeriv_eq_zero_of_notMem {χ f : Vec d → ℝ} (hsub : tsupport f ⊆ tsupport χ)
    {x : Vec d} (hx : x ∉ tsupport χ) (α : Fin d → ℕ) : multiCoordDeriv α f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    hx (hsub (tsupport_multiCoordDeriv_subset f α h))

omit [Fintype κ] in
theorem tsupport_systemG_subset {χ : Vec d → ℝ} (Abar : (Fin d → ℕ) → Matrix κ ι ℝ)
    (V : Vec d → ι → ℝ) (Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ) (α : Fin d → ℕ) (c : κ) :
    tsupport (fun y => systemG χ Abar V Y α y c) ⊆ tsupport χ := by
  have h : (fun y => systemG χ Abar V Y α y c) =
      -(fun y => χ y * (∑ i, Abar α c i * V y i + Y α α y c)) := rfl
  rw [h, tsupport_neg]
  exact tsupport_mul_subset_left

theorem systemk_fixed {k : ℕ} {Abar : (Fin d → ℕ) → Matrix κ ι ℝ} {P0 : ι → ℝ} {r : ℝ}
    {χ u : Vec d → ℝ} {V μ : Vec d → ι → ℝ}
    {Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ} {N M : ℝ}
    (h : SystemInput k Abar P0 r χ u V μ Y N) (hr : |r| ≤ 1) (hN0 : 0 ≤ N)
    (hM : ∀ θ : Fin d → ℕ, multiAbs θ ≤ k → ∀ x, |multiCoordDeriv θ χ x| ≤ M) :
    ∃ H : (Fin d → ℕ) → Vec d → κ → ℝ,
      (∀ β, ContDiff ℝ (⊤ : ℕ∞) (H β) ∧ HasCompactSupport (H β) ∧ tsupport (H β) ⊆ tsupport χ) ∧
      IsSystemK k Abar P0 (fun x => χ x * u x) (systemG χ Abar V Y) H ∧
      ∑ β ∈ lowIdx d k, ∫ x, piEuclideanNorm (H β x) ≤ (∑ c, remK k Abar P0 c M) * N := by
  have hc : ∀ c : κ, ∃ H : (Fin d → ℕ) → Vec d → ℝ, (∀ β, ContDiff ℝ (⊤ : ℕ∞) (H β)) ∧
      (∀ β, HasCompactSupport (H β)) ∧ (∀ β, tsupport (H β) ⊆ tsupport χ) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) (7 / 8), (∑ α ∈ Finset.Nat.antidiagonalTuple d k,
          (Abar α *ᵥ P0) c * multiCoordDeriv α (fun y => χ y * u y) x -
        ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
          multiCoordDeriv α (fun y => systemG χ Abar V Y α y c) x) =
        ∑ β ∈ lowIdx d k, multiCoordDeriv β (H β) x) ∧
      ∑ β ∈ lowIdx d k, ∫ x, |H β x| ≤ remK k Abar P0 c M * N :=
    fun c => (remainder_lowRep h hr hN0 hM c).2
  choose Hc h1 h2 h3 h4 h5 using hc
  have hsubχ : tsupport χ ⊆ euclideanBall (0 : Vec d) (7 / 8) :=
    h.hχs.trans (euclideanBall_mono (by norm_num) (by norm_num))
  refine ⟨fun β x c => Hc c β x, fun β => ?_, ?_, ?_⟩
  · have hsub : tsupport (fun x c => Hc c β x) ⊆ tsupport χ := by
      refine closure_minimal (fun x hx => ?_) (isClosed_tsupport χ)
      obtain ⟨c, hc'⟩ : ∃ c, Hc c β x ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hx (funext hne)
      exact h3 c β (subset_tsupport _ hc')
    exact ⟨contDiff_pi.2 fun c => h1 c β,
      IsCompact.of_isClosed_subset h.hχc (isClosed_tsupport _) hsub, hsub⟩
  · intro x
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    show _ = ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
        multiCoordDeriv α (fun y => systemG χ Abar V Y α y c) x +
      ∑ h' ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h',
        multiCoordDeriv β (fun y => Hc c β y) x
    by_cases hx : x ∈ euclideanBall (0 : Vec d) (7 / 8)
    · have e := h4 c x hx
      rw [sum_lowIdx] at e
      have e2 : ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
          multiCoordDeriv α (fun y => χ y * u y) x * (Abar α *ᵥ P0) c =
          ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (Abar α *ᵥ P0) c *
            multiCoordDeriv α (fun y => χ y * u y) x :=
        Finset.sum_congr rfl fun α _ => mul_comm _ _
      rw [e2]
      linarith
    · have hxχ : x ∉ tsupport χ := fun hh => hx (hsubχ hh)
      have z1 : ∀ α, multiCoordDeriv α (fun y => χ y * u y) x = 0 := fun α =>
        multiCoordDeriv_eq_zero_of_notMem (tsupport_mul_subset_left) hxχ α
      have z2 : ∀ α, multiCoordDeriv α (fun y => systemG χ Abar V Y α y c) x = 0 := fun α =>
        multiCoordDeriv_eq_zero_of_notMem (tsupport_systemG_subset Abar V Y α c) hxχ α
      have z3 : ∀ β, multiCoordDeriv β (fun y => Hc c β y) x = 0 := fun β =>
        multiCoordDeriv_eq_zero_of_notMem (h3 c β) hxχ β
      simp [z1, z2, z3]
  · have hcont : ∀ c β, Integrable (fun x => Hc c β x) := fun c β =>
      (h1 c β).continuous.integrable_of_hasCompactSupport (h2 c β)
    calc ∑ β ∈ lowIdx d k, ∫ x, piEuclideanNorm (Hc · β x)
        ≤ ∑ β ∈ lowIdx d k, ∑ c, ∫ x, |Hc c β x| := by
          refine Finset.sum_le_sum fun β _ => ?_
          rw [← integral_finsetSum _ fun c _ => (hcont c β).abs]
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
            piEuclideanNorm_nonneg _) (integrable_finsetSum _ fun c _ => (hcont c β).abs)
            (Filter.Eventually.of_forall fun x => piEuclideanNorm_le_sum_abs _)
      _ = ∑ c, ∑ β ∈ lowIdx d k, ∫ x, |Hc c β x| := Finset.sum_comm
      _ ≤ ∑ c, remK k Abar P0 c M * N := Finset.sum_le_sum fun c _ => h5 c
      _ = _ := by rw [Finset.sum_mul]

end

end AFree
