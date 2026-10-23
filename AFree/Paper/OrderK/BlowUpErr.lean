module

public import AFree.Paper.OrderK.BlowUpMollk
public import AFree.Paper.OrderK.BlowUpCut
public import AFree.Paper.OrderK.BlowUpRemainder

/-!
# Size of the coefficient errors

The coefficient error matrices
`F_{α,β} = ∂^{α-β}(Ã_α - Ā_α)` are `O(r)` on `B₁` and the mollified errors `Y_{α,β}` have `L¹(B_{7/8})`
norm `≤ C_A r (|P₀| + δ)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix PDE
open scoped ENNReal

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem multiCoordDeriv_sum_on {U : Set (Vec d)} (hU : IsOpen U) {ι' : Type*} (s : Finset ι')
    {F : ι' → Vec d → ℝ} (h : ∀ a ∈ s, SmOn U (F a)) (α : Fin d → ℕ) :
    Set.EqOn (multiCoordDeriv α (fun x => ∑ a ∈ s, F a x))
      (fun x => ∑ a ∈ s, multiCoordDeriv α (F a) x) U := by
  have key : ∀ l : List (Fin d), Set.EqOn (foldDeriv l α (fun x => ∑ a ∈ s, F a x))
      (fun x => ∑ a ∈ s, foldDeriv l α (F a) x) U := by
    intro l
    induction l with
    | nil => exact fun _ _ => rfl
    | cons i l ih =>
      intro x hx
      show (euclideanCoordDeriv i)^[α i] (foldDeriv l α (fun x => ∑ a ∈ s, F a x)) x = _
      rw [eqOn_iterD hU ih i (α i) hx]
      exact iterD_sum hU s (fun a ha => (h a ha).foldr α l) i (α i) hx
  exact key _

theorem multiCoordDeriv_const_of_ne (c : ℝ) {γ : Fin d → ℕ} (hγ : γ ≠ 0) :
    multiCoordDeriv γ (fun _ : Vec d => c) = fun _ => 0 := by
  have key : ∀ l : List (Fin d), foldDeriv l γ (fun _ : Vec d => c) =
      fun _ => if ∀ i ∈ l, γ i = 0 then c else 0 := by
    intro l
    induction l with
    | nil => simp [foldDeriv]
    | cons j l ih =>
      funext x
      show (euclideanCoordDeriv j)^[γ j] (foldDeriv l γ (fun _ : Vec d => c)) x = _
      rw [ih]
      by_cases hj : γ j = 0
      · simp [hj]
      · obtain ⟨n, hn⟩ : ∃ n, γ j = n + 1 := ⟨γ j - 1, by omega⟩
        rw [hn, Function.iterate_succ_apply]
        have h0 : euclideanCoordDeriv j (fun _ : Vec d => if ∀ i ∈ l, γ i = 0 then c else 0) =
            fun _ => 0 := by
          funext y; simp [euclideanCoordDeriv]
        rw [h0]
        have hz : ∀ m : ℕ, (euclideanCoordDeriv j)^[m] (fun _ : Vec d => (0 : ℝ)) =
            fun _ => 0 := by
          intro m
          induction m with
          | zero => rfl
          | succ m ihm =>
            have hd0 : euclideanCoordDeriv j (fun _ : Vec d => (0 : ℝ)) = fun _ => 0 := by
              funext y; simp [euclideanCoordDeriv]
            rw [Function.iterate_succ_apply, hd0]
            exact ihm
        rw [hz n]
        simp [hj]
  have h := key (List.finRange d)
  have hne : ¬ ∀ i ∈ List.finRange d, γ i = 0 := by
    intro hall
    exact hγ (funext fun i => hall i (List.mem_finRange i))
  rw [multiCoordDeriv_eq_foldDeriv, h]
  funext x
  simp only [hne, ite_false]

/-- `∂^γ (f - c) = ∂^γ f` on `U` for `γ ≠ 0`. -/
theorem multiCoordDeriv_sub_const {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : SmOn U f) (c : ℝ) {γ : Fin d → ℕ} (hγ : γ ≠ 0) :
    Set.EqOn (multiCoordDeriv γ (fun x => f x - c)) (multiCoordDeriv γ f) U := by
  intro x hx
  have hs : ∀ a ∈ (Finset.univ : Finset (Fin 2)), SmOn U (fun x => if a = 0 then f x else -c) :=
    fun a _ => by
      by_cases ha : a = 0
      · simpa [ha] using hf
      · simpa [ha] using smOn_const (U := U) (-c)
  have h := multiCoordDeriv_sum_on hU (Finset.univ : Finset (Fin 2)) hs γ hx
  have e : (fun x => ∑ a ∈ (Finset.univ : Finset (Fin 2)), if a = 0 then f x else -c) =
      fun x => f x - c := by
    funext y; simp [Fin.sum_univ_two, sub_eq_add_neg]
  rw [e] at h
  rw [h]
  simp only [Fin.sum_univ_two]
  have hc : multiCoordDeriv γ (fun _ : Vec d => -c) x = 0 := by
    rw [multiCoordDeriv_const_of_ne (-c) hγ]
  simp [hc]

/-- The coefficient error matrix `F_{α,β} = ∂^{α-β}(Ã_α - Ā_α)` with
`Ã_α(z) = A_α(x₀ + r z)` and `Ā_α = A_α(x₀)`. -/
def errF (x₀ : Vec d) (r : ℝ) (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ) (α β : Fin d → ℕ)
    (z : Vec d) : Matrix κ ι ℝ :=
  Matrix.of fun j i =>
    multiCoordDeriv (α - β) (fun w => A α (x₀ + r • w) j i - A α x₀ j i) z

/-- `f_{α,β} = 1_{B₁} F_{α,β} P_r`. -/
def errDensity (x₀ : Vec d) (r : ℝ) (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ) (P : Vec d → ι → ℝ)
    (α β : Fin d → ℕ) : Vec d → κ → ℝ :=
  (euclideanBall (0 : Vec d) 1).indicator fun z => errF x₀ r A α β z *ᵥ blowDensity x₀ r P z

/-- `Y_{α,β} = (f_{α,β} σ_r)_ε`. -/
def errY (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) (ε : ℝ) (σ : Measure (Vec d))
    (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ) (P : Vec d → ι → ℝ) (α β : Fin d → ℕ) :
    Vec d → κ → ℝ :=
  mollify ε (blowMeasure x₀ r c σ) (errDensity x₀ r A P α β)

/-- `sup_{B₁} |F_{α,β}| ≤ C_A r` (operator norm), for `0 < r ≤ r̄`. -/
theorem errF_bound {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {k : ℕ}
    {A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ}
    (hA : ∀ α j i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A α x j i) Ω) {x₀ : Vec d} {P0 : ι → ℝ}
    {c0 rb CA : ℝ} (hs : IsBlowSettingK Ω k A x₀ P0 c0 rb CA) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ rb)
    {α β : Fin d → ℕ} (hα : multiAbs α ≤ k) (hβ : β ∈ multiLE α) {z : Vec d}
    (hz : z ∈ euclideanBall (0 : Vec d) 1) (v : ι → ℝ) :
    piEuclideanNorm (errF x₀ r A α β z *ᵥ v) ≤ CA * r * piEuclideanNorm v := by
  have hzQ : ‖z‖ ≤ 1 := by
    have := euclideanBall_one_subset_closedBall_one hz
    simpa using this
  have hrQ : x₀ + r • z ∈ Metric.closedBall x₀ rb := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr0.le]
    nlinarith [norm_nonneg z]
  have hxΩ : x₀ + r • z ∈ Ω := hs.hQ hrQ
  have hCA := hs.hCA
  have hsm : ∀ j i, SmOn Ω (fun x => A α x j i) := fun j i x hx =>
    (hA α j i).contDiffAt (hΩ.mem_nhds hx)
  by_cases hαβ : β = α
  · subst hαβ
    have e : errF x₀ r A β β z = A β (x₀ + r • z) - A β x₀ := by
      ext j i
      simp [errF, multiCoordDeriv_zero, sub_self_pi]
    rw [e]
    refine (hs.hlip β hα _ hrQ v).trans ?_
    have h1 : ‖(x₀ + r • z) - x₀‖ ≤ r := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le]
      nlinarith [norm_nonneg z]
    have h2 : 0 ≤ piEuclideanNorm v := Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCA) h2
  · obtain ⟨γ, hγ⟩ : ∃ γ, γ = α - β := ⟨_, rfl⟩
    have hγ0 : γ ≠ 0 := by
      intro h0
      apply hαβ
      funext i
      have := congrFun h0 i
      have := mem_multiLE.1 hβ i
      simp [hγ] at *
      omega
    have hγk : multiAbs γ ≤ k := by rw [hγ]; exact (multiAbs_sub_le α β).trans hα
    have hU : IsOpen (affMap r x₀ ⁻¹' Ω) := hΩ.preimage (continuous_affMap r x₀)
    have hzU : z ∈ affMap r x₀ ⁻¹' Ω := by
      show r • z + x₀ ∈ Ω
      rwa [add_comm]
    have hent : ∀ j i, multiCoordDeriv γ (fun w => A α (x₀ + r • w) j i - A α x₀ j i) z =
        r ^ multiAbs γ * multiCoordDeriv γ (fun y => A α y j i) (x₀ + r • z) := by
      intro j i
      have hsm' : SmOn (affMap r x₀ ⁻¹' Ω) (fun w => A α (x₀ + r • w) j i) := by
        have := (hsm j i).comp_affMap r x₀
        refine fun w hw => ?_
        have h := this w hw
        have e : (fun z => A α (affMap r x₀ z) j i) = fun w => A α (x₀ + r • w) j i := by
          funext w; simp [affMap, add_comm]
        simpa [e] using h
      rw [multiCoordDeriv_sub_const hU hsm' _ hγ0 hzU]
      have e : (fun w => A α (x₀ + r • w) j i) = fun w => (fun y => A α y j i) (affMap r x₀ w) := by
        funext w; simp [affMap, add_comm]
      rw [e, multiCoordDeriv_comp_affMap hΩ (hsm j i) r x₀ γ hzU]
      simp [affMap, add_comm]
    have e : errF x₀ r A α β z = r ^ multiAbs γ •
        (Matrix.of fun j i => multiCoordDeriv γ (fun y => A α y j i) (x₀ + r • z)) := by
      ext j i
      simp [errF, hent, ← hγ]
    rw [e, Matrix.smul_mulVec, piEuclideanNorm_smul]
    have h3 := hs.hderiv α hα γ hγk _ hrQ v
    have h4 : r ^ multiAbs γ ≤ r := by
      have : multiAbs γ ≠ 0 := by
        intro h0
        apply hγ0
        funext i
        have : ∑ i, γ i = 0 := h0
        exact (Finset.sum_eq_zero_iff.1 this) i (Finset.mem_univ i)
      exact pow_le_of_le_one hr0.le (hr1.trans hs.hrb1) this
    rw [abs_of_nonneg (pow_nonneg hr0.le _)]
    calc r ^ multiAbs γ * piEuclideanNorm ((Matrix.of fun j i =>
          multiCoordDeriv γ (fun y => A α y j i) (x₀ + r • z)) *ᵥ v)
        ≤ r ^ multiAbs γ * (CA * piEuclideanNorm v) :=
          mul_le_mul_of_nonneg_left h3 (pow_nonneg hr0.le _)
      _ ≤ r * (CA * piEuclideanNorm v) :=
          mul_le_mul_of_nonneg_right h4 (mul_nonneg hCA (Real.sqrt_nonneg _))
      _ = CA * r * piEuclideanNorm v := by ring

end

end AFree
