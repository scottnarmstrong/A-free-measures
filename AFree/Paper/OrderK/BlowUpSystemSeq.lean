module

public import AFree.Paper.OrderK.BlowUpSystemK

/-!
# The cut-off lemma

The cut-off of the mollified blow-ups in divergence form, in the exact shape of the hypotheses of
strong constancy of order `k`.
-/

@[expose] public section

open MeasureTheory PDE Matrix Filter Topology

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem cutK_nonneg {M : ℝ} (hM : 0 ≤ M) (γ : Fin d → ℕ) : 0 ≤ cutK M γ :=
  mul_nonneg hM (Finset.sum_nonneg fun _ _ => multiChoose_nonneg _ _)

omit [Fintype κ] in
theorem remK_nonneg {M : ℝ} (hM : 0 ≤ M) (k : ℕ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (P0 : ι → ℝ)
    (c : κ) : 0 ≤ remK k Abar P0 c M := by
  have hc := cutK_nonneg (d := d) hM
  unfold remK remKD remKB remKC1 remKC2 remKTop
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) (add_nonneg ?_ ?_)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (abs_nonneg _) (hc _)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (abs_nonneg _) (hc _)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (abs_nonneg _) (hc _)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (abs_nonneg _) (hc _)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (abs_nonneg _) (hc _)
  · exact Finset.sum_nonneg fun _ _ => hc _

omit [Fintype κ] in
theorem systemG_eq_zero {χ : Vec d → ℝ} (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (V : Vec d → ι → ℝ)
    (Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ) (α : Fin d → ℕ) {x : Vec d} (hx : χ x = 0) :
    systemG χ Abar V Y α x = 0 := by
  funext c; simp [systemG, hx]

omit [Fintype κ] in
theorem tsupport_systemG_vec_subset {χ : Vec d → ℝ} (Abar : (Fin d → ℕ) → Matrix κ ι ℝ)
    (V : Vec d → ι → ℝ) (Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ) (α : Fin d → ℕ) :
    tsupport (systemG χ Abar V Y α) ⊆ tsupport χ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport χ)
  by_contra hxχ
  exact hx (systemG_eq_zero Abar V Y α (image_eq_zero_of_notMem_tsupport hxχ))

/-- There are `G_j^{(α)} = -χ(Ā_α V_j + Y_{j,α,α})` and `H_{j,β}` in `C_c^∞(ℝ^d; ℝ^κ)`
with support in `tsupport χ ⊆ B_{3/4}` such that `Σ_{|α|=k} A_α P₀ ∂^α w_j = Σ ∂^α G_j^{(α)} +
Σ_{|β|≤k-1} ∂^β H_{j,β}` on `ℝ^d` for `w_j = χ u_j`, `Σ_α ‖G_j^{(α)}‖_{L¹} → 0`,
`sup_j ‖H_{j,β}‖_{L¹} < ∞`, `w_j ≥ 0`, `tsupport w_j ⊆ closed B_{3/4}`, `sup_j ‖w_j‖_{L¹} ≤ 1`.
The hypotheses are the mollified equation (`hmoll`) and the smallness and concentration estimates; the output
is exactly the hypothesis list of strong constancy of order `k`. -/
theorem lem_systemk {k : ℕ} (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (P0 : ι → ℝ)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (hχs : tsupport χ ⊆ euclideanBall (0 : Vec d) (3 / 4))
    {r δ : ℕ → ℝ} (CA : ℝ) (hCA : 0 ≤ CA) (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (hrt : Tendsto r atTop (𝓝 0)) (hδ0 : ∀ j, 0 ≤ δ j) (hδt : Tendsto δ atTop (𝓝 0))
    {u : ℕ → Vec d → ℝ} {V μ : ℕ → Vec d → ι → ℝ}
    {Y : ℕ → (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ}
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (hu0 : ∀ j x, 0 ≤ u j x)
    (hV : ∀ j i, ContDiff ℝ (⊤ : ℕ∞) (fun x => V j x i))
    (hμs : ∀ j i, ContDiff ℝ (⊤ : ℕ∞) (fun x => μ j x i))
    (hY : ∀ j α β c, ContDiff ℝ (⊤ : ℕ∞) (fun x => Y j α β x c))
    (hμ : ∀ j x, μ j x = u j x • P0 + V j x)
    (hmoll : ∀ j, ∀ x ∈ euclideanBall (0 : Vec d) (7 / 8), ∀ c : κ,
      ∑ h ∈ Finset.range (k + 1), r j ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
          ∑ i, Abar α c i * multiCoordDeriv α (fun y => μ j y i) x =
        -(∑ h ∈ Finset.range (k + 1), r j ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
          ∑ β ∈ multiLE α, mollSign α β * multiCoordDeriv β (fun y => Y j α β y c) x))
    (hu1 : ∀ j, ∫ x in euclideanBall (0 : Vec d) (7 / 8), u j x ≤ 1)
    (hVs : ∀ j, ∫ x in euclideanBall (0 : Vec d) (7 / 8), piEuclideanNorm (V j x) ≤ δ j)
    (hμb : ∀ j, ∫ x in euclideanBall (0 : Vec d) (7 / 8), piEuclideanNorm (μ j x) ≤
      piEuclideanNorm P0 + δ j)
    (hYs : ∀ j α, multiAbs α ≤ k → ∀ β ∈ multiLE α,
      ∫ x in euclideanBall (0 : Vec d) (7 / 8), piEuclideanNorm (Y j α β x) ≤
        CA * r j * (piEuclideanNorm P0 + δ j)) :
    ∃ H : ℕ → (Fin d → ℕ) → Vec d → κ → ℝ,
      (∀ j, IsCc (fun x => χ x * u j x)) ∧ (∀ j x, 0 ≤ χ x * u j x) ∧
      (∀ j, tsupport (fun x => χ x * u j x) ⊆ euclideanClosedBall (0 : Vec d) (3 / 4)) ∧
      (∀ j α, ContDiff ℝ (⊤ : ℕ∞) (systemG χ Abar (V j) (Y j) α) ∧
        HasCompactSupport (systemG χ Abar (V j) (Y j) α)) ∧
      (∀ j β, ContDiff ℝ (⊤ : ℕ∞) (H j β) ∧ HasCompactSupport (H j β)) ∧
      (∀ j α, tsupport (systemG χ Abar (V j) (Y j) α) ⊆ euclideanBall (0 : Vec d) 1) ∧
      (∀ j, IsSystemK k Abar P0 (fun x => χ x * u j x) (systemG χ Abar (V j) (Y j)) (H j)) ∧
      Tendsto (fun j => sumL1 k (systemG χ Abar (V j) (Y j))) atTop (𝓝 0) ∧
      (∀ h ∈ Finset.range k, ∀ β ∈ Finset.Nat.antidiagonalTuple d h,
        ∃ C : ℝ, ∀ j, ∫ x, piEuclideanNorm (H j β x) ≤ C) ∧
      (∃ C : ℝ, ∀ j, ∫ x, |χ x * u j x| ≤ C) := by
  set P : ℝ := piEuclideanNorm P0 with hPdef
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  set η : ℕ → ℝ := fun j => CA * r j * (P + δ j) with hηdef
  have hη0 : ∀ j, 0 ≤ η j := fun j => mul_nonneg (mul_nonneg hCA (hr0 j)) (add_nonneg hP0 (hδ0 j))
  set N : ℕ → ℝ := fun j => 1 + δ j + (P + δ j) + η j with hNdef
  have hN0 : ∀ j, 0 ≤ N j := fun j => by
    have := hδ0 j; have := hη0 j; simp only [hNdef]; linarith
  have hNge : ∀ j, 1 ≤ N j ∧ δ j ≤ N j ∧ P + δ j ≤ N j ∧ η j ≤ N j := fun j => by
    have := hδ0 j; have := hη0 j
    simp only [hNdef]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨M, hM0, hM⟩ := exists_deriv_bound hχ hχc k
  -- continuity of the data
  have cV : ∀ j c, Continuous fun x => V j x c := fun j c => (hV j c).continuous
  have cμ : ∀ j c, Continuous fun x => μ j x c := fun j c => (hμs j c).continuous
  have cY : ∀ j α β c, Continuous fun x => Y j α β x c := fun j α β c => (hY j α β c).continuous
  -- the size bounds
  have hNV : ∀ j i, ∫ x in euclideanBall (0 : Vec d) (7 / 8), |V j x i| ≤ δ j :=
    fun j i => (setIntegral_abs_apply_le (cV j) i).trans (hVs j)
  have hNμ : ∀ j i, ∫ x in euclideanBall (0 : Vec d) (7 / 8), |μ j x i| ≤ P + δ j :=
    fun j i => (setIntegral_abs_apply_le (cμ j) i).trans (hμb j)
  have hNY : ∀ j α, multiAbs α ≤ k → ∀ β ∈ multiLE α, ∀ c,
      ∫ x in euclideanBall (0 : Vec d) (7 / 8), |Y j α β x c| ≤ η j :=
    fun j α hα β hβ c => (setIntegral_abs_apply_le (cY j α β) c).trans (hYs j α hα β hβ)
  have hNu : ∀ j, ∫ x in euclideanBall (0 : Vec d) (7 / 8), |u j x| ≤ 1 := fun j => by
    simp only [abs_of_nonneg (hu0 j _)]
    exact hu1 j
  have hinput : ∀ j, SystemInput k Abar P0 (r j) χ (u j) (V j) (μ j) (Y j) (N j) := fun j =>
    { hχ := hχ, hχc := hχc, hχs := hχs, hu := hu j, hV := hV j, hμs := hμs j, hY := hY j,
      hμ := hμ j, hmoll := hmoll j
      hNu := (hNu j).trans (hNge j).1
      hNV := fun i => (hNV j i).trans (hNge j).2.1
      hNμ := fun i => (hNμ j i).trans (hNge j).2.2.1
      hNY := fun α hα β hβ c => (hNY j α hα β hβ c).trans (hNge j).2.2.2 }
  have hfix : ∀ j, ∃ H : (Fin d → ℕ) → Vec d → κ → ℝ,
      (∀ β, ContDiff ℝ (⊤ : ℕ∞) (H β) ∧ HasCompactSupport (H β) ∧ tsupport (H β) ⊆ tsupport χ) ∧
      IsSystemK k Abar P0 (fun x => χ x * u j x) (systemG χ Abar (V j) (Y j)) H ∧
      ∑ β ∈ lowIdx d k, ∫ x, piEuclideanNorm (H β x) ≤ (∑ c, remK k Abar P0 c M) * N j :=
    fun j => systemk_fixed (hinput j) (by rw [abs_of_nonneg (hr0 j)]; exact hr1 j) (hN0 j) hM
  choose H hH1 hH2 hH3 using hfix
  have hsub34 : euclideanBall (0 : Vec d) (3 / 4) ⊆ euclideanBall 0 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  refine ⟨H, fun j => ⟨hχ.mul (hu j), hχc.mul_right⟩, fun j x => mul_nonneg (hχ0 x) (hu0 j x),
    fun j => (tsupport_mul_subset_left (f := χ) (g := u j)).trans
      (hχs.trans (euclideanBall_subset_euclideanClosedBall _ _)), fun j α => ?_,
    fun j β => ⟨(hH1 j β).1, (hH1 j β).2.1⟩, fun j α =>
      (tsupport_systemG_vec_subset Abar (V j) (Y j) α).trans (hχs.trans hsub34), hH2, ?_, ?_, ?_⟩
  · refine ⟨contDiff_pi.2 fun c => ?_, IsCompact.of_isClosed_subset hχc (isClosed_tsupport _)
      (tsupport_systemG_vec_subset Abar (V j) (Y j) α)⟩
    exact (hχ.mul ((ContDiff.sum fun i _ => contDiff_const.mul (hV j i)).add (hY j α α c))).neg
  · -- `Σ ‖G‖ → 0`
    set CG1 := ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ c, ∑ i, |Abar α c i|
    set CG2 := ∑ _α ∈ Finset.Nat.antidiagonalTuple d k, ∑ _c : κ, (1 : ℝ)
    have hlim : Tendsto (fun j => CG1 * δ j + CG2 * η j) atTop (𝓝 (CG1 * 0 + CG2 * 0)) := by
      have hηt : Tendsto η atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := CA)).mul hrt |>.mul (tendsto_const_nhds (x := P).add hδt)
        simpa [hηdef] using this
      exact (hδt.const_mul CG1).add (hηt.const_mul CG2)
    rw [mul_zero, mul_zero, add_zero] at hlim
    refine squeeze_zero (fun j => Finset.sum_nonneg fun α _ => integral_nonneg fun x =>
      piEuclideanNorm_nonneg _) (fun j => ?_) hlim
    exact sumL1_systemG_le (k := k) Abar hχ.continuous hχ0 hχ1 hχs hχc (cV j) (cY j)
      (hNV j) (fun α hα c => hNY j α hα.le α (mem_multiLE.2 fun i => le_rfl) c)
  · intro h' hh β hβ
    obtain ⟨B, hB⟩ : ∃ B, ∀ j, N j ≤ B := by
      have hNt : Tendsto N atTop (𝓝 (1 + 0 + (P + 0) + CA * 0 * (P + 0))) := by
        have h1 := (tendsto_const_nhds (x := (1 : ℝ))).add hδt
        have h2 := (tendsto_const_nhds (x := P)).add hδt
        have h3 := (tendsto_const_nhds (x := CA)).mul hrt |>.mul h2
        exact (h1.add h2).add h3
      obtain ⟨B, hB⟩ := hNt.bddAbove_range
      exact ⟨B, fun j => hB ⟨j, rfl⟩⟩
    have hK0 : 0 ≤ ∑ c, remK k Abar P0 c M := Finset.sum_nonneg fun c _ => remK_nonneg hM0 k Abar P0 c
    refine ⟨(∑ c, remK k Abar P0 c M) * B, fun j => ?_⟩
    have hβk : β ∈ lowIdx d k := by
      rw [mem_lowIdx]
      have := (Finset.Nat.mem_antidiagonalTuple.1 hβ)
      have hh' := Finset.mem_range.1 hh
      unfold multiAbs; omega
    calc ∫ x, piEuclideanNorm (H j β x)
        ≤ ∑ β' ∈ lowIdx d k, ∫ x, piEuclideanNorm (H j β' x) :=
          Finset.single_le_sum (f := fun β' => ∫ x, piEuclideanNorm (H j β' x))
            (fun _ _ => integral_nonneg fun x => piEuclideanNorm_nonneg _) hβk
      _ ≤ (∑ c, remK k Abar P0 c M) * N j := hH3 j
      _ ≤ (∑ c, remK k Abar P0 c M) * B := mul_le_mul_of_nonneg_left (hB j) hK0
  · refine ⟨1, fun j => ?_⟩
    exact (integral_abs_mul_cut_le hχ.continuous hχ0 hχ1 hχs (hu j).continuous).trans (by
      simpa only [abs_of_nonneg (hu0 j _)] using hu1 j)

end

end AFree
