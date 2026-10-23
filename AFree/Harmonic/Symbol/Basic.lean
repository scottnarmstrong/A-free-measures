module

public import AFree.Harmonic.Fourier
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Symbol classes `S^s` on `Vec d`

`IsSymbol s m`: `m` is smooth and `‖D^n m ξ‖ ≤ C_n (1 + |ξ|)^(s - n)` for every `n`.
The estimates are packaged level by level (`SymBound`) for functions with values in any normed
space, so that Leibniz-type arguments can use finitely many levels.
-/

@[expose] public section

open PDE

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The level-`n` symbol estimate of order `s` for a function `F` on `Vec d`. -/
def SymBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ℝ) (n : ℕ)
    (F : Vec d → E) : Prop :=
  ∃ C : ℝ, ∀ ξ : Vec d, ‖iteratedFDeriv ℝ n F ξ‖ ≤ C * (1 + vecEuclideanNorm ξ) ^ (s - n)

/-- Symbols of order `s`: smooth, with `‖D^n m ξ‖ ≤ C (1 + |ξ|)^(s - n)`. -/
def IsSymbol (s : ℝ) (m : Vec d → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) m ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ ξ : Vec d,
    ‖iteratedFDeriv ℝ n m ξ‖ ≤ C * (1 + vecEuclideanNorm ξ) ^ (s - n)

theorem one_add_vecEuclideanNorm_pos (ξ : Vec d) : 0 < 1 + vecEuclideanNorm ξ := by
  have := vecEuclideanNorm_nonneg ξ; linarith

theorem one_le_one_add_vecEuclideanNorm (ξ : Vec d) : 1 ≤ 1 + vecEuclideanNorm ξ := by
  have := vecEuclideanNorm_nonneg ξ; linarith

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem SymBound.nonneg {s : ℝ} {n : ℕ} {f : Vec d → E} (h : SymBound s n f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec d,
      ‖iteratedFDeriv ℝ n f ξ‖ ≤ C * (1 + vecEuclideanNorm ξ) ^ (s - n) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨|C|, abs_nonneg _, fun ξ => (hC ξ).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_abs_self _)
    (Real.rpow_nonneg (one_add_vecEuclideanNorm_pos ξ).le _)

theorem SymBound.mono {s s' : ℝ} (hs : s ≤ s') {n : ℕ} {f : Vec d → E} (h : SymBound s n f) :
    SymBound s' n f := by
  obtain ⟨C, hC0, hC⟩ := h.nonneg
  refine ⟨C, fun ξ => (hC ξ).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (one_le_one_add_vecEuclideanNorm ξ) (by linarith)) hC0

theorem SymBound.const (c : E) (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    SymBound s n (fun _ : Vec d => c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨‖c‖, fun ξ => ?_⟩
    simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
    have : (1 : ℝ) ≤ (1 + vecEuclideanNorm ξ) ^ s :=
      Real.one_le_rpow (one_le_one_add_vecEuclideanNorm ξ) hs
    nlinarith [norm_nonneg c]
  · refine ⟨0, fun ξ => ?_⟩
    rw [iteratedFDeriv_const_of_ne hn.ne']
    simp

theorem SymBound.add {s : ℝ} {n : ℕ} {f g : Vec d → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (h1 : SymBound s n f) (h2 : SymBound s n g) :
    SymBound s n (fun ξ => f ξ + g ξ) := by
  obtain ⟨C, hC⟩ := h1
  obtain ⟨C', hC'⟩ := h2
  refine ⟨C + C', fun ξ => ?_⟩
  have : iteratedFDeriv ℝ n (fun ξ => f ξ + g ξ) ξ =
      iteratedFDeriv ℝ n f ξ + iteratedFDeriv ℝ n g ξ :=
    iteratedFDeriv_add_apply (hf.contDiffAt.of_le (mod_cast le_top))
      (hg.contDiffAt.of_le (mod_cast le_top))
  rw [this, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC ξ) (hC' ξ))

/-- Leibniz rule for the symbol estimates, for a continuous bilinear pairing. -/
theorem SymBound.bilin (B : E →L[ℝ] F →L[ℝ] G) {s s' : ℝ} {f : Vec d → E} {g : Vec d → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (n : ℕ)
    (h1 : ∀ i ≤ n, SymBound s i f) (h2 : ∀ i ≤ n, SymBound s' i g) :
    SymBound (s + s') n (fun ξ => B (f ξ) (g ξ)) := by
  have h1' : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ (i ≤ n → ∀ ξ : Vec d,
      ‖iteratedFDeriv ℝ i f ξ‖ ≤ C * (1 + vecEuclideanNorm ξ) ^ (s - i)) := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨C, hC0, hC⟩ := (h1 i hi).nonneg; exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hi⟩
  have h2' : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ (i ≤ n → ∀ ξ : Vec d,
      ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + vecEuclideanNorm ξ) ^ (s' - i)) := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨C, hC0, hC⟩ := (h2 i hi).nonneg; exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hi⟩
  choose C1 hC1 hb1 using h1'
  choose C2 hC2 hb2 using h2'
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C1 i * C2 (n - i), fun ξ => ?_⟩
  have hle := B.norm_iteratedFDeriv_le_of_bilinear (𝕜 := ℝ) (hf.of_le (mod_cast le_top))
    (hg.of_le (mod_cast le_top)) ξ (n := n) (N := n) le_rfl
  refine hle.trans ?_
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (norm_nonneg B)
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hx := one_add_vecEuclideanNorm_pos ξ
  have hpow : (1 + vecEuclideanNorm ξ) ^ (s - (i : ℝ)) * (1 + vecEuclideanNorm ξ) ^ (s' - ((n - i : ℕ) : ℝ)) =
      (1 + vecEuclideanNorm ξ) ^ (s + s' - (n : ℝ)) := by
    rw [← Real.rpow_add hx, Nat.cast_sub hin]; congr 1; ring
  have a1 := hb1 i hin ξ
  have a2 := hb2 (n - i) (Nat.sub_le _ _) ξ
  have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ * ‖iteratedFDeriv ℝ (n - i) g ξ‖
      ≤ (n.choose i : ℝ) * (C1 i * (1 + vecEuclideanNorm ξ) ^ (s - (i : ℝ))) *
        (C2 (n - i) * (1 + vecEuclideanNorm ξ) ^ (s' - ((n - i : ℕ) : ℝ))) := by
        have p1 : 0 ≤ (1 + vecEuclideanNorm ξ) ^ (s - (i : ℝ)) := Real.rpow_nonneg hx.le _
        have e1 := hC1 i
        have e2 := hC2 (n - i)
        have nb := norm_nonneg (iteratedFDeriv ℝ i f ξ)
        exact mul_le_mul (mul_le_mul_of_nonneg_left a1 hc) a2 (norm_nonneg _)
          (mul_nonneg hc (mul_nonneg e1 p1))
    _ = (n.choose i : ℝ) * C1 i * C2 (n - i) * (1 + vecEuclideanNorm ξ) ^ (s + s' - (n : ℝ)) := by
        rw [← hpow]; ring

end

/-! ### Closure properties of `IsSymbol` -/

namespace IsSymbol

theorem bound {s : ℝ} {m : Vec d → ℂ} (hm : IsSymbol s m) (n : ℕ) : SymBound s n m := hm.2 n

theorem const (c : ℂ) {s : ℝ} (hs : 0 ≤ s) : IsSymbol s (fun _ : Vec d => c) :=
  ⟨contDiff_const, fun n => SymBound.const c s hs n⟩

theorem mul {s s' : ℝ} {m m' : Vec d → ℂ} (hm : IsSymbol s m) (hm' : IsSymbol s' m') :
    IsSymbol (s + s') (fun ξ => m ξ * m' ξ) :=
  ⟨hm.1.mul hm'.1, fun n =>
    SymBound.bilin (ContinuousLinearMap.mul ℝ ℂ) hm.1 hm'.1 n (fun i _ => hm.bound i)
      (fun i _ => hm'.bound i)⟩

theorem add {s : ℝ} {m m' : Vec d → ℂ} (hm : IsSymbol s m) (hm' : IsSymbol s m') :
    IsSymbol s (fun ξ => m ξ + m' ξ) :=
  ⟨hm.1.add hm'.1, fun n => SymBound.add hm.1 hm'.1 (hm.bound n) (hm'.bound n)⟩

theorem smul {s : ℝ} (c : ℂ) {m : Vec d → ℂ} (hm : IsSymbol s m) :
    IsSymbol s (fun ξ => c * m ξ) := by
  simpa using (const c (le_refl (0 : ℝ))).mul hm

theorem mono {s s' : ℝ} (h : s ≤ s') {m : Vec d → ℂ} (hm : IsSymbol s m) : IsSymbol s' m :=
  ⟨hm.1, fun n => (hm.bound n).mono h⟩

theorem zero (s : ℝ) : IsSymbol s (fun _ : Vec d => (0 : ℂ)) :=
  ⟨contDiff_const, fun n => ⟨0, fun ξ => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [iteratedFDeriv_const_of_ne hn.ne']; simp⟩⟩

theorem sum {s : ℝ} {ι : Type*} (t : Finset ι) {m : ι → Vec d → ℂ}
    (hm : ∀ i ∈ t, IsSymbol s (m i)) : IsSymbol s (fun ξ => ∑ i ∈ t, m i ξ) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using zero (d := d) s
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hm a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hm i (Finset.mem_insert_of_mem hi))

theorem hasTemperateGrowth {s : ℝ} {m : Vec d → ℂ} (hm : IsSymbol s m) :
    Function.HasTemperateGrowth m := by
  refine ⟨hm.1, fun n => ?_⟩
  obtain ⟨C, hC0, hC⟩ := (hm.bound n).nonneg
  set k : ℕ := ⌈s - n⌉₊ with hk
  refine ⟨k, C * (1 + Real.sqrt d) ^ k, fun ξ => ?_⟩
  have h1 : 1 + vecEuclideanNorm ξ ≤ (1 + Real.sqrt d) * (1 + ‖ξ‖) := by
    have := vecEuclideanNorm_le_sqrt_natCast_mul_norm ξ
    have h0 := Real.sqrt_nonneg (d : ℝ)
    nlinarith [norm_nonneg ξ]
  have h2 : (1 + vecEuclideanNorm ξ) ^ (s - n) ≤ (1 + vecEuclideanNorm ξ) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_one_add_vecEuclideanNorm ξ) (Nat.le_ceil _)
  calc ‖iteratedFDeriv ℝ n m ξ‖ ≤ C * (1 + vecEuclideanNorm ξ) ^ (s - n) := hC ξ
    _ ≤ C * (1 + vecEuclideanNorm ξ) ^ k := mul_le_mul_of_nonneg_left h2 hC0
    _ ≤ C * ((1 + Real.sqrt d) * (1 + ‖ξ‖)) ^ k := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (one_add_vecEuclideanNorm_pos ξ).le h1 k) hC0
    _ = C * (1 + Real.sqrt d) ^ k * (1 + ‖ξ‖) ^ k := by rw [mul_pow]; ring

end IsSymbol

end

end AFree
