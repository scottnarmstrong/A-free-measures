module

public import AFree.MetricCurrents.Basic
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Lipschitz partitions of unity on a grid
-/

@[expose] public section

open scoped BigOperators NNReal

namespace AFree

open PDE

/-- The hat function `hat(s) = max(0, 1 - |s|)`. -/
noncomputable def hat (s : ℝ) : ℝ := max 0 (1 - |s|)

/-- `χ_J(y) = ∏_l hat(y_l / r - J_l)` for `J ∈ ℤ^m`, `r > 0`. -/
noncomputable def gridChi {m : ℕ} (r : ℝ) (J : Fin m → ℤ) (y : Vec m) : ℝ :=
  ∏ l, hat (y l / r - J l)




private lemma hat_nonneg (s : ℝ) : 0 ≤ hat s := le_max_left _ _

private lemma hat_le_one (s : ℝ) : hat s ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg s])

private lemma hat_ne_zero_iff (s : ℝ) : hat s ≠ 0 ↔ |s| < 1 := by
  unfold hat
  constructor
  · intro h
    by_contra hs
    exact h (max_eq_left (by linarith [not_lt.1 hs]))
  · intro hs
    exact (lt_max_of_lt_right (by linarith)).ne'

private lemma abs_hat_sub_le (a b : ℝ) : |hat a - hat b| ≤ |a - b| := by
  unfold hat
  rw [max_comm 0 (1 - |a|), max_comm 0 (1 - |b|)]
  refine (abs_max_sub_max_le_abs (1 - |a|) (1 - |b|) 0).trans ?_
  have : (1 - |a|) - (1 - |b|) = |b| - |a| := by ring
  rw [this]
  exact (abs_abs_sub_abs_le_abs_sub b a).trans (le_of_eq (abs_sub_comm _ _))

private lemma hat_support (s : ℝ) (j : ℤ) (hj : hat (s - j) ≠ 0) :
    j ∈ ({⌊s⌋, ⌊s⌋ + 1} : Finset ℤ) := by
  rw [hat_ne_zero_iff, abs_lt] at hj
  have h1 : (j : ℝ) < ⌊s⌋ + 2 := by linarith [Int.lt_floor_add_one s, hj.1]
  have h2 : (⌊s⌋ : ℝ) - 1 < j := by linarith [Int.floor_le s, hj.2]
  have h1' : j < ⌊s⌋ + 2 := by exact_mod_cast h1
  have h2' : ⌊s⌋ - 1 < j := by exact_mod_cast h2
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

private lemma sum_hat_finset (s : ℝ) (F : Finset ℤ) (hF : ∀ j : ℤ, hat (s - j) ≠ 0 → j ∈ F) :
    ∑ j ∈ F, hat (s - j) = 1 := by
  set n := ⌊s⌋ with hn
  have hf0 := Int.fract_nonneg s
  have hf1 := Int.fract_lt_one s
  have hfr : Int.fract s = s - n := rfl
  have key : ∑ j ∈ ({n, n + 1} : Finset ℤ), hat (s - j) = 1 := by
    rw [Finset.sum_pair (by omega)]
    have a1 : hat (s - n) = 1 - Int.fract s := by
      unfold hat; rw [hfr, abs_of_nonneg (by linarith)]
      exact max_eq_right (by linarith)
    have a2 : hat (s - ((n + 1 : ℤ) : ℝ)) = Int.fract s := by
      unfold hat; push_cast
      have : s - (n + 1) = Int.fract s - 1 := by rw [hfr]; ring
      rw [this, abs_of_nonpos (by linarith), max_eq_right (by linarith)]
      ring
    rw [a1, a2]; ring
  rw [← key]
  have e1 : ∑ j ∈ F, hat (s - j) = ∑ j ∈ F ∪ {n, n + 1}, hat (s - j) := by
    refine Finset.sum_subset Finset.subset_union_left fun j _ hj => ?_
    by_contra h
    exact hj (hF j h)
  have e2 : ∑ j ∈ ({n, n + 1} : Finset ℤ), hat (s - j) = ∑ j ∈ F ∪ {n, n + 1}, hat (s - j) := by
    refine Finset.sum_subset Finset.subset_union_right fun j _ hj => ?_
    by_contra h
    exact hj (hat_support s j h)
  rw [e1, e2]

private lemma abs_prod_sub_prod_le {m : ℕ} (p q : Fin m → ℝ) (hp0 : ∀ l, 0 ≤ p l)
    (hp1 : ∀ l, p l ≤ 1) (hq0 : ∀ l, 0 ≤ q l) (hq1 : ∀ l, q l ≤ 1) :
    |∏ l, p l - ∏ l, q l| ≤ ∑ l, |p l - q l| := by
  have : ∀ S : Finset (Fin m), |∏ l ∈ S, p l - ∏ l ∈ S, q l| ≤ ∑ l ∈ S, |p l - q l| := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hQ0 : 0 ≤ ∏ l ∈ S, q l := Finset.prod_nonneg fun l _ => hq0 l
      have hQ1 : ∏ l ∈ S, q l ≤ 1 := Finset.prod_le_one₀ (fun l _ => hq0 l) fun l _ => hq1 l
      set P := ∏ l ∈ S, p l
      set Q := ∏ l ∈ S, q l
      have e : p a * P - q a * Q = p a * (P - Q) + (p a - q a) * Q := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hp0 a), abs_of_nonneg hQ0]
      have h1 : p a * |P - Q| ≤ |P - Q| := by
        nlinarith [abs_nonneg (P - Q), hp1 a, hp0 a]
      have h2 : |p a - q a| * Q ≤ |p a - q a| := by
        nlinarith [abs_nonneg (p a - q a)]
      linarith
  exact this Finset.univ

private lemma gridChi_nonneg' {m : ℕ} (r : ℝ) (J : Fin m → ℤ) (y : Vec m) : 0 ≤ gridChi r J y :=
  Finset.prod_nonneg fun _ _ => hat_nonneg _

private lemma gridChi_le_one' {m : ℕ} (r : ℝ) (J : Fin m → ℤ) (y : Vec m) : gridChi r J y ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => hat_nonneg _) fun _ _ => hat_le_one _

private lemma gridChi_ne_zero_iff {m : ℕ} (r : ℝ) (J : Fin m → ℤ) (y : Vec m) :
    gridChi r J y ≠ 0 ↔ ∀ l, hat (y l / r - J l) ≠ 0 := by
  unfold gridChi
  rw [Finset.prod_ne_zero_iff]
  simp

/-- The `ℓ¹` Lipschitz bound `|χ_J(y) - χ_J(y')| ≤ r⁻¹ ∑_l |y_l - y'_l|`. -/
theorem gridChi_abs_sub_le {m : ℕ} {r : ℝ} (hr : 0 < r) (J : Fin m → ℤ) (y y' : Vec m) :
    |gridChi r J y - gridChi r J y'| ≤ r⁻¹ * ∑ l, |y l - y' l| := by
  unfold gridChi
  refine (abs_prod_sub_prod_le _ _ (fun _ => hat_nonneg _) (fun _ => hat_le_one _)
    (fun _ => hat_nonneg _) (fun _ => hat_le_one _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  refine (abs_hat_sub_le _ _).trans ?_
  have : y l / r - J l - (y' l / r - J l) = (y l - y' l) / r := by ring
  rw [this, abs_div, abs_of_pos hr, div_eq_inv_mul]

private lemma sum_abs_le_sqrt {m : ℕ} (y y' : Vec m) :
    ∑ l, |y l - y' l| ≤ Real.sqrt m * vecEuclideanNorm (y - y') := by
  have h1 : (∑ l, |y l - y' l|) ^ 2 ≤ (m : ℝ) * ∑ l, (y l - y' l) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun l => |y l - y' l|)
    simpa [sq_abs] using this
  have h2 : (Real.sqrt m * vecEuclideanNorm (y - y')) ^ 2 = (m : ℝ) * ∑ l, (y l - y' l) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), vecEuclideanNorm_sq, vecNormSq_eq_sum_sq]
    rfl
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (vecEuclideanNorm_nonneg _)) two_ne_zero).1 (h2 ▸ h1)

/-- The grid functions `χ_J`: bounded Euclidean `(√m / r)`-Lipschitz, with values in
`[0,1]`; `χ_J(y) ≠ 0` forces `|y_l - r J_l| < r`; they sum to one, over any finset containing the
support at `y`; and a bounded set meets only finitely many supports. -/
theorem grid_partition_of_unity {m : ℕ} {r : ℝ} (hr : 0 < r) :
    (∀ J : Fin m → ℤ, IsBddLipFun (gridChi r J)) ∧
    (∀ (J : Fin m → ℤ) (y : Vec m), 0 ≤ gridChi r J y ∧ gridChi r J y ≤ 1) ∧
    (∀ J : Fin m → ℤ, IsEuclLipschitzWith ⟨Real.sqrt m / r, by positivity⟩ (gridChi r J)) ∧
    (∀ (J : Fin m → ℤ) (y : Vec m), gridChi r J y ≠ 0 → ∀ l, |y l - r * J l| < r) ∧
    (∀ (y : Vec m) (F : Finset (Fin m → ℤ)), (∀ J : Fin m → ℤ, gridChi r J y ≠ 0 → J ∈ F) →
      ∑ J ∈ F, gridChi r J y = 1) ∧
    (∀ R : ℝ, {J : Fin m → ℤ | ∃ y : Vec m, ‖y‖ ≤ R ∧ gridChi r J y ≠ 0}.Finite) := by
  have hlip : ∀ J : Fin m → ℤ,
      IsEuclLipschitzWith ⟨Real.sqrt m / r, by positivity⟩ (gridChi r J) := by
    intro J y y'
    refine (gridChi_abs_sub_le hr J y y').trans ?_
    refine (mul_le_mul_of_nonneg_left (sum_abs_le_sqrt y y') (inv_nonneg.2 hr.le)).trans ?_
    show _ ≤ Real.sqrt m / r * _
    rw [div_eq_inv_mul, mul_assoc]
  have hsupp : ∀ (J : Fin m → ℤ) (y : Vec m), gridChi r J y ≠ 0 → ∀ l, |y l - r * J l| < r := by
    intro J y hy l
    have := (hat_ne_zero_iff _).1 ((gridChi_ne_zero_iff r J y).1 hy l)
    have e : y l - r * J l = r * (y l / r - J l) := by field_simp
    rw [e, abs_mul, abs_of_pos hr]
    nlinarith
  refine ⟨fun J => ⟨⟨_, hlip J⟩, 1, fun y => ?_⟩,
    fun J y => ⟨gridChi_nonneg' r J y, gridChi_le_one' r J y⟩, hlip, hsupp, ?_, ?_⟩
  · rw [abs_of_nonneg (gridChi_nonneg' r _ y)]; exact gridChi_le_one' r _ y
  · intro y F hF
    let G : Fin m → Finset ℤ := fun l => {⌊y l / r⌋, ⌊y l / r⌋ + 1}
    let P : Finset (Fin m → ℤ) := Fintype.piFinset G
    have hsubP : ∀ J, gridChi r J y ≠ 0 → J ∈ P := by
      intro J hJ
      rw [Fintype.mem_piFinset]
      exact fun l => hat_support _ _ ((gridChi_ne_zero_iff r J y).1 hJ l)
    have e1 : ∑ J ∈ F, gridChi r J y = ∑ J ∈ F ∪ P, gridChi r J y :=
      Finset.sum_subset Finset.subset_union_left fun J _ hJ => by
        by_contra h; exact hJ (hF J h)
    have e2 : ∑ J ∈ P, gridChi r J y = ∑ J ∈ F ∪ P, gridChi r J y :=
      Finset.sum_subset Finset.subset_union_right fun J _ hJ => by
        by_contra h; exact hJ (hsubP J h)
    rw [e1, ← e2]
    unfold gridChi
    rw [← Finset.prod_univ_sum G (fun l j => hat (y l / r - (j : ℝ)))]
    refine Finset.prod_eq_one fun l _ => ?_
    exact sum_hat_finset _ (G l) fun j hj => hat_support _ _ hj
  · intro R
    let N : ℤ := ⌈R / r⌉ + 1
    refine (Finset.finite_toSet (Fintype.piFinset fun _ : Fin m => Finset.Icc (-N) N)).subset ?_
    rintro J ⟨y, hy, hJ⟩
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro l
    rw [Finset.mem_Icc]
    have h1 := (hat_ne_zero_iff _).1 ((gridChi_ne_zero_iff r J y).1 hJ l)
    rw [abs_lt] at h1
    have hyl : |y l| ≤ R := (norm_le_pi_norm y l).trans hy
    have hyl' := abs_le.1 hyl
    have hc := Int.le_ceil (R / r)
    have hyr : y l / r ≤ R / r := div_le_div_of_nonneg_right hyl'.2 hr.le
    have hyr' : -(R / r) ≤ y l / r := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right hyl'.1 hr.le
    have a1 : (J l : ℝ) < N := by push_cast [N]; linarith [h1.1]
    have a2 : (-N : ℝ) < J l := by push_cast [N]; linarith [h1.2]
    constructor
    · have : -N < J l := by exact_mod_cast a2
      omega
    · have : J l < N := by exact_mod_cast a1
      omega

end AFree
