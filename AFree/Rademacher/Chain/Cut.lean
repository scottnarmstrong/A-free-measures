module

public import AFree.Rademacher.Cutoff
public import AFree.Curves.Perturb

/-!
# The cut-off perturbation (AM Lemma 4.11)

Perturbation of a Lipschitz function by a cut-off, with prescribed directional derivative on a cone-null compact set.
-/

@[expose] public section

open PDE Filter Topology Set

namespace AFree.Rademacher

variable {d : ℕ}

/-- The product `g = φ g₀` of the cut-off `φ` and a perturbation
`g₀` has the estimates (i)–(iii) of [AM, Lemma 4.11], given the size and slope bounds on `φ`
(`|∇φ| ≤ c/(r'-r)`) and the smallness of `ε₀ = sup g₀`. -/
theorem perturbcut_product_estimates {e : Vec d} (he : vecEuclideanNorm e = 1) {t ε₀ M ε' : ℝ}
    {φ g₀ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hg₀ : ContDiff ℝ (⊤ : ℕ∞) g₀)
    (hφ01 : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (hgε : ∀ x, 0 ≤ g₀ x ∧ g₀ x ≤ ε₀)
    (hgrad : ∀ x, vecEuclideanNorm (euclGrad φ x) ≤ M) (hMε : ε₀ * M ≤ ε')
    (hmono : ∀ x, 0 ≤ fderiv ℝ g₀ x e ∧ fderiv ℝ g₀ x e ≤ 1)
    (hW : ∀ x w, vecDot w e = 0 → |fderiv ℝ g₀ x w| ≤ t * vecEuclideanNorm w)
    (hMt : ε₀ * M ≤ t) :
    (∀ x, -ε' ≤ fderiv ℝ (fun y => φ y * g₀ y) x e ∧
      fderiv ℝ (fun y => φ y * g₀ y) x e ≤ 1 + ε') ∧
    ∀ x w, vecDot w e = 0 → |fderiv ℝ (fun y => φ y * g₀ y) x w| ≤ (t + t) * vecEuclideanNorm w := by
  have hdφ : ∀ x, DifferentiableAt ℝ φ x := fun x => hφ.differentiable (by simp) x
  have hdg : ∀ x, DifferentiableAt ℝ g₀ x := fun x => hg₀.differentiable (by simp) x
  have hd : ∀ x w, fderiv ℝ (fun y => φ y * g₀ y) x w =
      φ x * fderiv ℝ g₀ x w + g₀ x * fderiv ℝ φ x w := by
    intro x w
    rw [fderiv_fun_mul (hdφ x) (hdg x)]
    simp
  have hφw : ∀ x w, |fderiv ℝ φ x w| ≤ M * vecEuclideanNorm w := by
    intro x w
    rw [← vecDot_euclGrad]
    exact (abs_vecDot_le_vecEuclideanNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (hgrad x) (vecEuclideanNorm_nonneg _))
  have hg0w : ∀ x w, |g₀ x * fderiv ℝ φ x w| ≤ ε₀ * M * vecEuclideanNorm w := by
    intro x w
    rw [abs_mul, abs_of_nonneg (hgε x).1]
    calc g₀ x * |fderiv ℝ φ x w| ≤ ε₀ * (M * vecEuclideanNorm w) :=
          mul_le_mul (hgε x).2 (hφw x w) (abs_nonneg _) ((hgε x).1.trans (hgε x).2)
      _ = _ := by ring
  refine ⟨fun x => ?_, fun x w hw => ?_⟩
  · rw [hd]
    have h1 := hg0w x e
    rw [he, mul_one] at h1
    have h2 := abs_le.1 h1
    have h3 : 0 ≤ φ x * fderiv ℝ g₀ x e := mul_nonneg (hφ01 x).1 (hmono x).1
    have h4 : φ x * fderiv ℝ g₀ x e ≤ 1 :=
      (by simpa using mul_le_mul (hφ01 x).2 (hmono x).2 (hmono x).1 zero_le_one)
    constructor <;> linarith [h2.1, h2.2]
  · rw [hd]
    have h1 := hg0w x w
    have h2 : |φ x * fderiv ℝ g₀ x w| ≤ t * vecEuclideanNorm w := by
      rw [abs_mul, abs_of_nonneg (hφ01 x).1]
      calc φ x * |fderiv ℝ g₀ x w| ≤ 1 * (t * vecEuclideanNorm w) :=
            mul_le_mul (hφ01 x).2 (hW x w hw) (abs_nonneg _) zero_le_one
        _ = _ := by ring
    calc _ ≤ |φ x * fderiv ℝ g₀ x w| + |g₀ x * fderiv ℝ φ x w| := abs_add_le _ _
      _ ≤ t * vecEuclideanNorm w + ε₀ * M * vecEuclideanNorm w := add_le_add h2 h1
      _ ≤ _ := by nlinarith [vecEuclideanNorm_nonneg w]

/-- [AM, Lemma 4.11], with upper bound `1 + ε` for `D_e g`. Let `x̄ ∈ ℝ^d`,
`0 < r < r'`, `e` a unit vector, `α ∈ (0, π/2)`, `K ⊆ B̄(x̄, r)` a compact `C(e, α)`-null set and
`ε > 0`. There is a smooth `g` with `‖g‖_sup ≤ ε` and `supp g ⊆ B̄(x̄, r')`;
`-ε ≤ D_e g ≤ 1 + ε` on `ℝ^d` and `D_e g = 1` on `K`; and `|d_W g| ≤ 2/tan α` for `W = e^⊥`
(in the form `|g'(x) w| ≤ (2 / tan α) |w|` for `w ⊥ e`). -/
theorem lem_perturbcut {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {xb : Vec d} {r r' : ℝ} (hr : 0 < r) (hrr' : r < r')
    {K : Set (Vec d)} (hK : IsCompact K) (hKr : K ⊆ Metric.closedBall xb r)
    (hnull : IsCNull (cone e α) K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ ε) ∧
      tsupport g ⊆ Metric.closedBall xb r' ∧
      (∀ x, -ε ≤ fderiv ℝ g x e ∧ fderiv ℝ g x e ≤ 1 + ε) ∧
      (∀ x ∈ K, fderiv ℝ g x e = 1) ∧
      ∀ x w, vecDot w e = 0 → |fderiv ℝ g x w| ≤ (2 / Real.tan α) * vecEuclideanNorm w := by
  have htpos : 0 < Real.tan α := Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2
  obtain ⟨c₁, hc₁, hcut⟩ := cutoff_function d
  obtain ⟨φ, hφ, hφ01, hφ1, -, hφs, hφg⟩ := hcut xb r r' hr hrr'
  have hrr'0 : 0 < r' - r := sub_pos.2 hrr'
  set M := c₁ / (r' - r) with hM
  set ε₀ := min ε (min (ε / (M + 1)) (1 / (Real.tan α * (M + 1)))) with hε₀
  have hM0 : 0 ≤ M := div_nonneg hc₁ hrr'0.le
  have hε₀pos : 0 < ε₀ := lt_min hε (lt_min (by positivity) (by positivity))
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  have hε₀M : ε₀ * M ≤ ε := by
    have h1 : ε₀ ≤ ε / (M + 1) := (min_le_right _ _).trans (min_le_left _ _)
    calc ε₀ * M ≤ ε / (M + 1) * M := mul_le_mul_of_nonneg_right h1 hM0
      _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  have hε₀t : ε₀ * M ≤ 1 / Real.tan α := by
    have h1 : ε₀ ≤ 1 / (Real.tan α * (M + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    calc ε₀ * M ≤ 1 / (Real.tan α * (M + 1)) * M := mul_le_mul_of_nonneg_right h1 hM0
      _ ≤ 1 / Real.tan α := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) htpos]
        nlinarith
  obtain ⟨g₀, hg₀, hgε, hmono, ⟨U, hUo, hKU, hU⟩, hW⟩ :=
    perturb_of_cnull he hα hα2 hK hnull hε₀pos
  have hest := perturbcut_product_estimates he (ε' := ε) (t := 1 / Real.tan α) hφ hg₀ hφ01 hgε hφg
    hε₀M hmono hW hε₀t
  refine ⟨fun y => φ y * g₀ y, hφ.mul hg₀, fun x => ?_, ?_, hest.1, fun x hx => ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg (hφ01 x).1, abs_of_nonneg (hgε x).1]
    calc φ x * g₀ x ≤ 1 * ε₀ := mul_le_mul (hφ01 x).2 (hgε x).2 (hgε x).1 zero_le_one
      _ ≤ ε := by linarith
  · exact (tsupport_mul_subset_left).trans hφs
  · have hxK : ‖x - xb‖ < r + (r' - r) / 3 := by
      have := Metric.mem_closedBall.1 (hKr hx)
      rw [dist_eq_norm] at this
      linarith
    have hev : (fun y => φ y * g₀ y) =ᶠ[𝓝 x] g₀ := by
      have hopen : IsOpen {y : Vec d | ‖y - xb‖ < r + (r' - r) / 3} :=
        isOpen_lt (by fun_prop) continuous_const
      filter_upwards [hopen.mem_nhds hxK] with y hy
      simp [hφ1 y hy]
    rw [hev.fderiv_eq]
    exact hU x (hKU hx)
  · intro x w hw
    have := hest.2 x w hw
    have h2 : (1 / Real.tan α + 1 / Real.tan α) = 2 / Real.tan α := by ring
    rwa [h2] at this

end AFree.Rademacher
