module

public import AFree.Paper.OrderK.BlowUpErrInt
public import AFree.Paper.OrderK.BlowUpSystem

/-!
# The mollified equation of order `k`

Testing the rescaled equation against `ψ = φ_ε(x - ·)` gives
`Σ_h r^{k-h} Σ_{|α|=h} Ā_α ∂^α μ^ε = -Σ_h r^{k-h} Σ_{|α|=h} Σ_{β≤α} (-1)^{|α-β|} (α β) ∂^β Y^ε_{α,β}`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix PDE
open scoped ENNReal

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The test function `ψ(y) = φ_ε(x - y)` has support in `B₁` for `x ∈ B_{7/8}`, `ε ≤ 1/8`. -/
theorem tsupport_mollPsi_subset {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) (7 / 8)) :
    tsupport (fun y : Vec d => scaledMollifier ε (x - y)) ⊆ euclideanBall (0 : Vec d) 1 := by
  have h1 : tsupport (fun y : Vec d => scaledMollifier ε (x - y)) =
      (fun y => x - y) ⁻¹' tsupport (scaledMollifier (d := d) ε) :=
    tsupport_comp_eq_preimage (scaledMollifier (d := d) ε) (Homeomorph.subLeft x)
  rw [h1]
  intro y hy
  have hy' := tsupport_scaledMollifier_subset hε hy
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hε, sub_zero] at hy'
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)] at hx
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num), sub_zero]
  have h2 := vecEuclideanNorm_add_le x (-(x - y))
  rw [vecEuclideanNorm_neg, ← sub_eq_add_neg, sub_sub_cancel] at h2
  rw [sub_zero] at hx
  linarith

theorem isTestFunctionOn_mollPsi {Ω : Set (Vec d)} (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (hΩ : Metric.closedBall x₀ r ⊆ Ω) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) (7 / 8)) :
    IsTestFunctionOn (blowMap x₀ r '' Ω) (fun y => scaledMollifier ε (x - y)) := by
  refine ⟨(contDiff_scaledMollifier ε).comp (contDiff_const.sub contDiff_id), ?_, ?_⟩
  · exact (hasCompactSupport_scaledMollifier hε).comp_homeomorph (Homeomorph.subLeft x)
  · exact (tsupport_mollPsi_subset hε hε8 hx).trans
      (euclideanBall_one_subset_closedBall_one.trans (closedBall_one_subset_blowMap_image x₀ hr hΩ))

theorem mollify_apply_coord {ε : ℝ} (hε : 0 < ε) {τ : Measure (Vec d)} {f : Vec d → ι → ℝ}
    (hf : Integrable f τ) (x : Vec d) (i : ι) :
    mollify ε τ f x i = mollify ε τ (fun y => f y i) x := by
  have hint : Integrable (fun y => scaledMollifier ε (x - y) • f y) τ :=
    integrable_kernel (contDiff_scaledMollifier ε).continuous
      (hasCompactSupport_scaledMollifier hε) hf x
  have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integral_comp_comm hint)
  simp only [mollify, ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  exact this.symm

theorem integral_deriv_mollPsi {ε : ℝ} (hε : 0 < ε) {τ : Measure (Vec d)} [IsFiniteMeasure τ]
    {f : Vec d → ℝ} (hf : Integrable f τ) (α : Fin d → ℕ) (x : Vec d) :
    ∫ z, multiCoordDeriv α (fun y => scaledMollifier ε (x - y)) z * f z ∂τ =
      (-1 : ℝ) ^ multiAbs α * multiCoordDeriv α (mollify ε τ f) x := by
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (scaledMollifier (d := d) ε) := contDiff_scaledMollifier ε
  have e : (fun y : Vec d => scaledMollifier ε (x - y)) =
      fun y => scaledMollifier ε (affMap (-1) x y) := by
    funext y; simp [affMap, sub_eq_add_neg, add_comm]
  have hd : ∀ z, multiCoordDeriv α (fun y => scaledMollifier ε (x - y)) z =
      (-1 : ℝ) ^ multiAbs α * multiCoordDeriv α (scaledMollifier ε) (x - z) := by
    intro z
    rw [e]
    have := multiCoordDeriv_comp_affMap isOpen_univ (smOn_univ_iff.2 hΦ) (-1 : ℝ) x α
      (Set.mem_univ z)
    rw [this]
    simp [affMap, sub_eq_add_neg, add_comm]
  rw [(lem_mollk hε τ (ι := Unit)).1 f hf α x, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hd, mul_assoc]

omit [Fintype ι] [Fintype κ] in
theorem expand_psiA {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hΩr : Metric.closedBall x₀ r ⊆ Ω) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8)
    {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) (7 / 8)) (α : Fin d → ℕ) (e : κ) (i : ι)
    (z : Vec d) :
    multiCoordDeriv α (fun w => scaledMollifier ε (x - w) * A α (x₀ + r • w) e i) z =
      A α x₀ e i * multiCoordDeriv α (fun w => scaledMollifier ε (x - w)) z +
        ∑ β ∈ multiLE α, multiChoose α β *
          (multiCoordDeriv β (fun w => scaledMollifier ε (x - w)) z * errF x₀ r A α β z e i) := by
  set ψ : Vec d → ℝ := fun y => scaledMollifier ε (x - y) with hψdef
  have hψ : IsTestFunctionOn (blowMap x₀ r '' Ω) ψ := isTestFunctionOn_mollPsi x₀ hr hΩr hε hε8 hx
  have hts : tsupport ψ ⊆ euclideanBall (0 : Vec d) 1 := tsupport_mollPsi_subset hε hε8 hx
  have hTΩ : IsOpen (blowMap x₀ r '' Ω) := isOpen_blowMap_image hΩ x₀ hr.ne'
  have hsm : SmOn Ω (fun y => A α y e i) := fun y hy => (hA α e i).contDiffAt (hΩ.mem_nhds hy)
  have hB : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => A α (x₀ + r • w) e i) (blowMap x₀ r '' Ω) := by
    refine (hA α e i).comp (contDiffOn_const.add (contDiffOn_id.const_smul r)) ?_
    rintro w ⟨y, hy, rfl⟩
    have : x₀ + r • blowMap x₀ r y = y := by
      simp [blowMap, smul_smul, mul_inv_cancel₀ hr.ne']
    simpa [this] using hy
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun w => ψ w * A α (x₀ + r • w) e i) :=
    (lem_smoothext hTΩ hψ hB).1
  have hfun : (fun w => ψ w * A α (x₀ + r • w) e i) =
      fun w => A α x₀ e i * ψ w + ψ w * (A α (x₀ + r • w) e i - A α x₀ e i) := by
    funext w; ring
  have hE : ContDiff ℝ (⊤ : ℕ∞) (fun w => ψ w * (A α (x₀ + r • w) e i - A α x₀ e i)) := by
    have := hg.sub (contDiff_const.mul hψ.1 : ContDiff ℝ (⊤ : ℕ∞) fun w => A α x₀ e i * ψ w)
    convert this using 1
    funext w; ring
  rw [hfun, multiCoordDeriv_add_global (contDiff_const.mul hψ.1) hE,
    multiCoordDeriv_const_mul hψ.1]
  beta_reduce
  congr 1
  by_cases hz : z ∈ euclideanBall (0 : Vec d) 1
  · have hzQ : ∀ w ∈ euclideanBall (0 : Vec d) 1, x₀ + r • w ∈ Ω := by
      intro w hw
      have hwQ : ‖w‖ ≤ 1 := by
        have := euclideanBall_one_subset_closedBall_one hw
        simpa using this
      refine hΩr ?_
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hr.le]
      nlinarith [norm_nonneg w]
    have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
    have hAt : SmOn (euclideanBall (0 : Vec d) 1) (fun w => A α (x₀ + r • w) e i) := by
      have := hsm.comp_affMap r x₀
      intro w hw
      have h := this w (by show r • w + x₀ ∈ Ω; rw [add_comm]; exact hzQ w hw)
      have e' : (fun z => A α (affMap r x₀ z) e i) = fun w => A α (x₀ + r • w) e i := by
        funext w; simp [affMap, add_comm]
      simpa [e'] using h
    have hEs : SmOn (euclideanBall (0 : Vec d) 1)
        (fun w => A α (x₀ + r • w) e i - A α x₀ e i) := hAt.sub (smOn_const _)
    have hψs : SmOn (euclideanBall (0 : Vec d) 1) ψ := (smOn_univ_iff.2 hψ.1).mono (Set.subset_univ _)
    rw [multiCoordDeriv_mul hU hψs hEs α hz]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp [errF]
  · have hzψ : z ∉ tsupport ψ := fun h => hz (hts h)
    have h0 : ∀ β, multiCoordDeriv β ψ z = 0 := fun β =>
      multiCoordDeriv_eq_zero_of_notMem (χ := ψ) subset_rfl hzψ β
    rw [multiCoordDeriv_eq_zero_of_notMem (χ := ψ)
      ((tsupport_mul_subset_left (f := ψ) (g := fun w => A α (x₀ + r • w) e i -
        A α x₀ e i)).trans subset_rfl) hzψ α]
    simp [h0]

theorem multiAbs_sub_add {α β : Fin d → ℕ} (h : ∀ i, β i ≤ α i) :
    multiAbs (α - β) + multiAbs β = multiAbs α := by
  unfold multiAbs
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by have := h i; simp; omega

theorem integral_psiA {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {k : ℕ}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω)
    {σ : Measure (Vec d)} [IsFiniteMeasure σ] {P : Vec d → ι → ℝ} (hPm : Measurable P)
    (hPi : Integrable P σ) {x₀ : Vec d} {P0 : ι → ℝ}
    {c0 rb CA : ℝ} (hs : IsBlowSettingK Ω k A x₀ P0 c0 rb CA) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ rb)
    {c : ℝ≥0∞} (hc : c ≠ ∞) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) (7 / 8)) (e : κ) {α : Fin d → ℕ} (hα : multiAbs α ≤ k) :
    ∫ z, ∑ i, multiCoordDeriv α (fun w => scaledMollifier ε (x - w) * A α (x₀ + r • w) e i) z *
        blowDensity x₀ r P z i ∂blowMeasure x₀ r c σ =
      (-1 : ℝ) ^ multiAbs α * ∑ i, A α x₀ e i * multiCoordDeriv α
          (fun y => mollify ε (blowMeasure x₀ r c σ) (blowDensity x₀ r P) y i) x +
        ∑ β ∈ multiLE α, multiChoose α β * ((-1 : ℝ) ^ multiAbs β *
          multiCoordDeriv β (fun y => errY x₀ r c ε σ A P α β y e) x) := by
  have hΩr : Metric.closedBall x₀ r ⊆ Ω :=
    (Metric.closedBall_subset_closedBall hr1).trans hs.hQ
  set τ := blowMeasure x₀ r c σ with hτ
  have hfin := isFiniteMeasure_blowMeasure x₀ r hc σ
  have hψ := isTestFunctionOn_mollPsi (Ω := Ω) x₀ hr0 hΩr hε hε8 hx
  have hts := tsupport_mollPsi_subset hε hε8 hx
  have hPd := integrable_blowDensity x₀ hr0.ne' hc hPi (c := c)
  have hPc : ∀ i, Integrable (fun z => blowDensity x₀ r P z i) τ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hPd
  set ψ : Vec d → ℝ := fun y => scaledMollifier ε (x - y) with hψdef
  have hψcc : ∀ β, IsCc (multiCoordDeriv β ψ) := fun β =>
    isCc_multiCoordDeriv ⟨hψ.1, hψ.2.1⟩ β
  have hψb : ∀ β, ∃ C : ℝ, ∀ y, ‖multiCoordDeriv β ψ y‖ ≤ C := fun β =>
    (hψcc β).1.continuous.bounded_above_of_compact_support (hψcc β).2
  have hfi : ∀ β, β ∈ multiLE α → ∀ j,
      Integrable (fun z => errDensity x₀ r A P α β z j) τ := fun β hβ j =>
    integrable_pi_iff.1 (integrable_errDensity hΩ hA hs hr0 hr1 hPm hPi hc hα hβ) j
  have hi1 : ∀ i, Integrable (fun z => multiCoordDeriv α ψ z * blowDensity x₀ r P z i) τ :=
    fun i => (hPc i).bdd_mul (hψcc α).1.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (hψb α).choose_spec)
  have hi2 : ∀ β, β ∈ multiLE α →
      Integrable (fun z => multiCoordDeriv β ψ z * errDensity x₀ r A P α β z e) τ :=
    fun β hβ => (hfi β hβ e).bdd_mul (hψcc β).1.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (hψb β).choose_spec)
  -- pointwise form of the integrand
  have hpt : ∀ z, ∑ i, multiCoordDeriv α (fun w => ψ w * A α (x₀ + r • w) e i) z *
        blowDensity x₀ r P z i =
      ∑ i, A α x₀ e i * (multiCoordDeriv α ψ z * blowDensity x₀ r P z i) +
        ∑ β ∈ multiLE α, multiChoose α β *
          (multiCoordDeriv β ψ z * errDensity x₀ r A P α β z e) := by
    intro z
    have hD : ∀ β, multiCoordDeriv β ψ z * errDensity x₀ r A P α β z e =
        multiCoordDeriv β ψ z * ∑ i, errF x₀ r A α β z e i * blowDensity x₀ r P z i := by
      intro β
      by_cases hz : z ∈ euclideanBall (0 : Vec d) 1
      · simp [errDensity, Set.indicator_of_mem hz, Matrix.mulVec, dotProduct]
      · have hzψ : z ∉ tsupport ψ := fun h => hz (hts h)
        have := multiCoordDeriv_eq_zero_of_notMem (χ := ψ) (f := ψ) subset_rfl hzψ β
        simp [this]
    have hexp : ∀ i, multiCoordDeriv α (fun w => ψ w * A α (x₀ + r • w) e i) z =
        A α x₀ e i * multiCoordDeriv α ψ z +
          ∑ β ∈ multiLE α, multiChoose α β *
            (multiCoordDeriv β ψ z * errF x₀ r A α β z e i) := fun i =>
      expand_psiA hΩ hA x₀ hr0 hΩr hε hε8 hx α e i z
    simp only [hD, hexp, add_mul, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_add (integrable_finsetSum _ fun i _ => (hi1 i).const_mul _)
    (integrable_finsetSum _ fun β hβ => (hi2 β hβ).const_mul _),
    integral_finsetSum _ fun i _ => (hi1 i).const_mul _,
    integral_finsetSum _ fun β hβ => (hi2 β hβ).const_mul _]
  have hP1 : ∀ i, ∫ z, A α x₀ e i * (multiCoordDeriv α ψ z * blowDensity x₀ r P z i) ∂τ =
      A α x₀ e i * ((-1 : ℝ) ^ multiAbs α * multiCoordDeriv α
        (fun y => mollify ε τ (blowDensity x₀ r P) y i) x) := by
    intro i
    rw [integral_const_mul, integral_deriv_mollPsi hε (hPc i) α x]
    congr 3
    funext y
    exact (mollify_apply_coord hε hPd y i).symm
  have hP2 : ∀ β ∈ multiLE α, ∫ z, multiChoose α β *
      (multiCoordDeriv β ψ z * errDensity x₀ r A P α β z e) ∂τ =
      multiChoose α β * ((-1 : ℝ) ^ multiAbs β *
        multiCoordDeriv β (fun y => errY x₀ r c ε σ A P α β y e) x) := by
    intro β hβ
    rw [integral_const_mul, integral_deriv_mollPsi hε (hfi β hβ e) β x]
    congr 3
    funext y
    exact (mollify_apply_coord hε (integrable_errDensity hΩ hA hs hr0 hr1 hPm hPi hc hα hβ) y e).symm
  rw [Finset.sum_congr rfl fun i _ => hP1 i, Finset.sum_congr rfl hP2, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sign_aux {α β : Fin d → ℕ} (h : ∀ i, β i ≤ α i) :
    (-1 : ℝ) ^ multiAbs α * (-1 : ℝ) ^ multiAbs β = (-1 : ℝ) ^ multiAbs (α - β) := by
  rw [← multiAbs_sub_add h, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- For `ε ∈ (0, 1/8]`, `x ∈ B_{7/8}` and `e ∈ κ`, with `μ^ε = (P_r σ_r)_ε` and
`Y^ε_{α,β} = (f_{α,β} σ_r)_ε`:
`Σ_h r^{k-h} Σ_{|α|=h} Ā_α ∂^α μ^ε(x) = -Σ_h r^{k-h} Σ_{|α|=h} Σ_{β≤α} (-1)^{|α-β|} (α β) ∂^β Y^ε_{α,β}(x)`
(component `e`). -/
theorem lem_mollvar {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {k : ℕ}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω)
    {σ : Measure (Vec d)} [IsFiniteMeasure σ] {P : Vec d → ι → ℝ} (hPm : Measurable P)
    (hPi : Integrable P σ) (h : IsFreePairVar Ω k A σ P) {x₀ : Vec d} {P0 : ι → ℝ}
    {c0 rb CA : ℝ} (hs : IsBlowSettingK Ω k A x₀ P0 c0 rb CA) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ rb)
    {c : ℝ≥0∞} (hc : c ≠ ∞) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) (7 / 8)) (e : κ) :
    ∑ h' ∈ Finset.range (k + 1), r ^ (k - h') * ∑ α ∈ Finset.Nat.antidiagonalTuple d h',
        ∑ i, A α x₀ e i * multiCoordDeriv α
          (fun y => mollify ε (blowMeasure x₀ r c σ) (blowDensity x₀ r P) y i) x =
      -(∑ h' ∈ Finset.range (k + 1), r ^ (k - h') *
        ∑ α ∈ Finset.Nat.antidiagonalTuple d h', ∑ β ∈ multiLE α, mollSign α β *
          multiCoordDeriv β (fun y => errY x₀ r c ε σ A P α β y e) x) := by
  have hΩr : Metric.closedBall x₀ r ⊆ Ω :=
    (Metric.closedBall_subset_closedBall hr1).trans hs.hQ
  set τ := blowMeasure x₀ r c σ with hτ
  have hfin := isFiniteMeasure_blowMeasure x₀ r hc σ
  have hψ := isTestFunctionOn_mollPsi (Ω := Ω) x₀ hr0 hΩr hε hε8 hx
  have hts := tsupport_mollPsi_subset hε hε8 hx
  have key := lem_blowupk_B5k hΩ hA h x₀ hr0 c hψ e
  have hPd := integrable_blowDensity x₀ hr0.ne' hc hPi (c := c)
  have hPc : ∀ i, Integrable (fun z => blowDensity x₀ r P z i) τ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hPd
  -- bounded derivatives of `ψ`
  have hψcc : ∀ β, IsCc (multiCoordDeriv β (fun y => scaledMollifier ε (x - y))) := fun β =>
    isCc_multiCoordDeriv ⟨hψ.1, hψ.2.1⟩ β
  have hψb : ∀ β, ∃ C : ℝ, ∀ y, ‖multiCoordDeriv β (fun y => scaledMollifier ε (x - y)) y‖ ≤ C :=
    fun β => (hψcc β).1.continuous.bounded_above_of_compact_support (hψcc β).2
  have hterm : ∀ h' ∈ Finset.range (k + 1), (-1 : ℝ) ^ h' * r ^ (k - h') *
      ∑ α ∈ Finset.Nat.antidiagonalTuple d h', ∫ z, ∑ i : ι,
        multiCoordDeriv α (fun w => scaledMollifier ε (x - w) * A α (x₀ + r • w) e i) z *
          blowDensity x₀ r P z i ∂τ =
      r ^ (k - h') * ∑ α ∈ Finset.Nat.antidiagonalTuple d h', ∑ i,
        A α x₀ e i * multiCoordDeriv α
          (fun y => mollify ε τ (blowDensity x₀ r P) y i) x +
      r ^ (k - h') * ∑ α ∈ Finset.Nat.antidiagonalTuple d h', ∑ β ∈ multiLE α,
        mollSign α β * multiCoordDeriv β (fun y => errY x₀ r c ε σ A P α β y e) x := by
    intro h' hh'
    have hle : h' ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hh')
    have hJ : ∀ α ∈ Finset.Nat.antidiagonalTuple d h', ∫ z, ∑ i : ι,
        multiCoordDeriv α (fun w => scaledMollifier ε (x - w) * A α (x₀ + r • w) e i) z *
          blowDensity x₀ r P z i ∂τ =
        (-1 : ℝ) ^ h' * ∑ i, A α x₀ e i * multiCoordDeriv α
          (fun y => mollify ε τ (blowDensity x₀ r P) y i) x +
        ∑ β ∈ multiLE α, multiChoose α β * ((-1 : ℝ) ^ multiAbs β *
          multiCoordDeriv β (fun y => errY x₀ r c ε σ A P α β y e) x) := by
      intro α hα
      have hαa : multiAbs α = h' := by
        rw [Finset.Nat.mem_antidiagonalTuple] at hα; exact hα
      rw [← hαa]
      exact integral_psiA hΩ hA hPm hPi hs hr0 hr1 hc hε hε8 hx e (hαa ▸ hle)
    rw [Finset.sum_congr rfl hJ, Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
    have hsq : ((-1 : ℝ) ^ h') * (-1 : ℝ) ^ h' = 1 := by rw [← mul_pow]; simp
    congr 1
    · conv_rhs => rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      linear_combination (r ^ (k - h') * ∑ i : ι, A α x₀ e i * multiCoordDeriv α
          (fun y => mollify ε τ (blowDensity x₀ r P) y i) x) * hsq
    · conv_rhs => rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      have hαa : multiAbs α = h' := by
        rw [Finset.Nat.mem_antidiagonalTuple] at hα; exact hα
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β hβ => ?_
      have hs' := sign_aux (mem_multiLE.1 hβ)
      rw [hαa] at hs'
      unfold mollSign
      rw [← hs']
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib] at key
  exact eq_neg_of_add_eq_zero_left key

end

end AFree
