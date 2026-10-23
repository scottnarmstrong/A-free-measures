module

public import AFree.Paper.OrderK.BlowUpBad
public import AFree.Paper.OrderK.BlowUpLow
public import AFree.Paper.BlowUp
public import AFree.Measure.PolarFacts

/-!
# The setting of the order-`k` blow-up

The constants `c₀`, `r̄`, `C_A` at the good
point `x₀`, with `P₀ = P(x₀) ∉ Λ_{x₀}`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix PDE

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem exists_forall_abs_le_finset {T : Type*} (s : Finset T) {Q : Set (Vec d)}
    (hQ : IsCompact Q) {f : T → Vec d → ℝ} (hf : ∀ t ∈ s, ContinuousOn (f t) Q) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ s, ∀ x ∈ Q, |f t x| ≤ L := by
  classical
  have : ∀ t, ∃ C : ℝ, t ∈ s → ∀ x ∈ Q, |f t x| ≤ C := fun t => by
    by_cases ht : t ∈ s
    · obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn (hf t ht)
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose C hC using this
  refine ⟨∑ t ∈ s, |C t|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun t ht x hx => ?_⟩
  exact (hC t ht x hx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun t => |C t|) (fun _ _ => abs_nonneg _) ht))

theorem sum_abs_le_sqrt_card_mul (v : ι → ℝ) :
    ∑ i, |v i| ≤ Real.sqrt (Fintype.card ι) * piEuclideanNorm v := by
  have h := sum_mul_le_piEuclideanNorm_mul (fun i => |v i|) (fun _ : ι => (1 : ℝ))
  have e1 : piEuclideanNorm (fun i => |v i|) = piEuclideanNorm v := by
    unfold piEuclideanNorm; simp only [abs_mul_abs_self]
  have e2 : piEuclideanNorm (fun _ : ι => (1 : ℝ)) = Real.sqrt (Fintype.card ι) := by
    unfold piEuclideanNorm; simp
  simp only [mul_one] at h
  rw [e1, e2, mul_comm] at h
  exact h

theorem piEuclideanNorm_mulVec_le (M : Matrix κ ι ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hM : ∀ j i, |M j i| ≤ L) (v : ι → ℝ) :
    piEuclideanNorm (M *ᵥ v) ≤
      Real.sqrt (Fintype.card κ * Fintype.card ι) * L * piEuclideanNorm v := by
  have hB0 : 0 ≤ L * (Real.sqrt (Fintype.card ι) * piEuclideanNorm v) :=
    mul_nonneg hL (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hsup : ‖M *ᵥ v‖ ≤ L * (Real.sqrt (Fintype.card ι) * piEuclideanNorm v) := by
    refine (pi_norm_le_iff_of_nonneg hB0).2 fun j => ?_
    rw [Real.norm_eq_abs]
    calc |(M *ᵥ v) j| = |∑ i, M j i * v i| := rfl
      _ ≤ ∑ i, |M j i * v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, L * |v i| := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hM j i) (abs_nonneg _)
      _ = L * ∑ i, |v i| := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_card_mul v) hL
  calc piEuclideanNorm (M *ᵥ v) ≤ Real.sqrt (Fintype.card κ) * ‖M *ᵥ v‖ := piEuclideanNorm_le _
    _ ≤ Real.sqrt (Fintype.card κ) * (L * (Real.sqrt (Fintype.card ι) * piEuclideanNorm v)) :=
        mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _)]; ring

theorem abs_sub_le_of_coordDeriv_bound {g : Vec d → ℝ} {Q : Set (Vec d)} (hQ : Convex ℝ Q)
    (hdiff : ∀ y ∈ Q, DifferentiableAt ℝ g y) {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ l y, y ∈ Q → |euclideanCoordDeriv l g y| ≤ L) {x₀ x : Vec d} (hx₀ : x₀ ∈ Q)
    (hx : x ∈ Q) : |g x - g x₀| ≤ d * L * ‖x - x₀‖ := by
  have hb : ∀ y ∈ Q, ‖fderiv ℝ g y‖ ≤ d * L := by
    intro y hy
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hL) fun v => ?_
    have hv : v = ∑ l, v l • basisVec l := by
      ext i; simp [basisVec, Finset.sum_apply, Pi.single_apply]
    have h1 : fderiv ℝ g y v = ∑ l, v l * euclideanCoordDeriv l g y := by
      conv_lhs => rw [hv]
      simp only [map_sum, map_smul, smul_eq_mul]
      rfl
    rw [h1, Real.norm_eq_abs]
    calc |∑ l, v l * euclideanCoordDeriv l g y| ≤ ∑ l, |v l * euclideanCoordDeriv l g y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin d, ‖v‖ * L := Finset.sum_le_sum fun l _ => by
          rw [abs_mul]
          exact mul_le_mul (by simpa using norm_le_pi_norm v l) (hD l y hy) (abs_nonneg _)
            (norm_nonneg _)
      _ = d * L * ‖v‖ := by simp; ring
  have := hQ.norm_image_sub_le_of_norm_fderiv_le hdiff hb hx₀ hx
  rwa [Real.norm_eq_abs] at this

/-- The data of the setting: `c₀` (the ellipticity (iii') of [DPR, Section 2.3] for `Ā_α`, `P₀`), the radius
`r̄ ∈ (0,1]` with `Q_{r̄}(x₀) ⊆ Ω`, and `C_A` bounding the derivatives of the coefficients and their
oscillation on `Q_{r̄}(x₀)` (in the operator norm). -/
structure IsBlowSettingK (Ω : Set (Vec d)) (k : ℕ) (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ)
    (x₀ : Vec d) (P0 : ι → ℝ) (c0 rb CA : ℝ) : Prop where
  hc0 : 0 < c0
  hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤
    piEuclideanNorm (symbA k (fun α => A α x₀) P0 ξ)
  hrb0 : 0 < rb
  hrb1 : rb ≤ 1
  hQ : Metric.closedBall x₀ rb ⊆ Ω
  hCA : 0 ≤ CA
  hderiv : ∀ α, multiAbs α ≤ k → ∀ γ, multiAbs γ ≤ k → ∀ x ∈ Metric.closedBall x₀ rb,
    ∀ v : ι → ℝ, piEuclideanNorm ((Matrix.of fun (j : κ) (i : ι) =>
      multiCoordDeriv γ (fun y => A α y j i) x) *ᵥ v) ≤ CA * piEuclideanNorm v
  hlip : ∀ α, multiAbs α ≤ k → ∀ x ∈ Metric.closedBall x₀ rb, ∀ v : ι → ℝ,
    piEuclideanNorm ((A α x - A α x₀) *ᵥ v) ≤ CA * ‖x - x₀‖ * piEuclideanNorm v

/-- The constants of the setting exist at `x₀ ∈ Ω` with `P₀ ∉ Λ_{x₀}`. -/
theorem exists_blowSettingK (hd : 0 < d) {Ω : Set (Vec d)} (hΩ : IsOpen Ω) (k : ℕ)
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω) {x₀ : Vec d} (hx₀ : x₀ ∈ Ω)
    {P0 : ι → ℝ} (hP0 : P0 ∉ waveCone k (fun α => A α x₀)) :
    ∃ c0 rb CA : ℝ, IsBlowSettingK Ω k A x₀ P0 c0 rb CA := by
  obtain ⟨c0, hc0, hell⟩ := (lem_conek hd k).2.1 (fun α => A α x₀) P0 hP0
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  set rb : ℝ := min (ρ / 2) 1 with hrb
  have hrb0 : 0 < rb := lt_min (by positivity) one_pos
  have hrb1 : rb ≤ 1 := min_le_right _ _
  have hQΩ : Metric.closedBall x₀ rb ⊆ Ω := fun y hy =>
    hρΩ (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy)
      (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ))))
  set Q : Set (Vec d) := Metric.closedBall x₀ rb with hQ
  have hQc : IsCompact Q := isCompact_closedBall _ _
  have hsm : ∀ α j i, SmOn Ω (fun x => A α x j i) := fun α j i x hx =>
    (hA α j i).contDiffAt (hΩ.mem_nhds hx)
  have hcont : ∀ f : Vec d → ℝ, SmOn Ω f → ContinuousOn f Q := fun f hf x hx =>
    (hf x (hQΩ hx)).continuousAt.continuousWithinAt
  obtain ⟨L1, hL1, hL1b⟩ := exists_forall_abs_le_finset
    (lowIdx d (k + 1) ×ˢ ((Finset.univ : Finset κ) ×ˢ ((Finset.univ : Finset ι) ×ˢ
      lowIdx d (k + 1)))) hQc
    (f := fun t x => multiCoordDeriv t.2.2.2 (fun y => A t.1 y t.2.1 t.2.2.1) x)
    (fun t _ => hcont _ ((hsm _ _ _).multi _))
  obtain ⟨L2, hL2, hL2b⟩ := exists_forall_abs_le_finset
    (lowIdx d (k + 1) ×ˢ ((Finset.univ : Finset κ) ×ˢ ((Finset.univ : Finset ι) ×ˢ
      (Finset.univ : Finset (Fin d))))) hQc
    (f := fun t x => euclideanCoordDeriv t.2.2.2 (fun y => A t.1 y t.2.1 t.2.2.1) x)
    (fun t _ => hcont _ ((hsm _ _ _).D _))
  set L := L1 + L2 with hLdef
  have hL0 : 0 ≤ L := add_nonneg hL1 hL2
  set sq : ℝ := Real.sqrt (Fintype.card κ * Fintype.card ι) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hlow : ∀ α : Fin d → ℕ, multiAbs α ≤ k → α ∈ lowIdx d (k + 1) := fun α hα =>
    mem_lowIdx.2 (by omega)
  refine ⟨c0, rb, sq * (d * L + L), ⟨hc0, hell, hrb0, hrb1, hQΩ,
    mul_nonneg hsq0 (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hL0) hL0), ?_, ?_⟩⟩
  · intro α hα γ hγ x hx v
    refine (piEuclideanNorm_mulVec_le _ (L := L) hL0 (fun j i => ?_) v).trans ?_
    · have := hL1b (α, j, i, γ) (Finset.mem_product.2 ⟨hlow α hα, Finset.mem_product.2
        ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨Finset.mem_univ _, hlow γ hγ⟩⟩⟩) x hx
      exact this.trans (by linarith)
    · refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      refine mul_le_mul_of_nonneg_left ?_ hsq0
      have : 0 ≤ (d : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL0
      linarith
  · intro α hα x hx v
    have hLip : ∀ j i, |(A α x - A α x₀) j i| ≤ d * L * ‖x - x₀‖ := by
      intro j i
      have := abs_sub_le_of_coordDeriv_bound (g := fun y => A α y j i) (Q := Q)
        (convex_closedBall x₀ rb) (fun y hy => ((hsm α j i) y (hQΩ hy)).differentiableAt (by simp))
        hL0 (fun l y hy => by
          have := hL2b (α, j, i, l) (Finset.mem_product.2 ⟨hlow α hα, Finset.mem_product.2
            ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩⟩) y hy
          exact this.trans (by linarith)) (Metric.mem_closedBall_self hrb0.le) hx
      simpa using this
    refine (piEuclideanNorm_mulVec_le _ (L := d * L * ‖x - x₀‖)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hL0) (norm_nonneg _)) hLip v).trans ?_
    have h1 : 0 ≤ ‖x - x₀‖ := norm_nonneg _
    have h2 : 0 ≤ piEuclideanNorm v := Real.sqrt_nonneg _
    have h3 : 0 ≤ (d : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL0
    calc sq * (d * L * ‖x - x₀‖) * piEuclideanNorm v
        = (sq * (d * L)) * ‖x - x₀‖ * piEuclideanNorm v := by ring
      _ ≤ (sq * (d * L + L)) * ‖x - x₀‖ * piEuclideanNorm v := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ h1) h2
          exact mul_le_mul_of_nonneg_left (by linarith) hsq0

end

end AFree
