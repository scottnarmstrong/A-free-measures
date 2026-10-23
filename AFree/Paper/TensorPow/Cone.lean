module

public import AFree.Paper.TensorPow.Curl

/-!
# The wave cone of the curl-type operator (Fonseca-Müller computation)

The wave cone of the curl-type operator on `Dʳu` consists of the tensors `a ⊗ ξ^{⊗r}`, as in
Fonseca–Müller; used in the proof of [DPR, Theorem 1.6].
-/

public section

open Matrix

namespace AFree

open PDE

variable {ℓ d r : ℕ}

/-- The relation extracted from the symbol: `ξ_j P(k, α[h↦i]) = ξ_i P(k, α[h↦j])`. -/
theorem curlr_symbol_relation {ξ : Vec d} {P : CurlrCol ℓ d r → ℝ}
    (hP : (∑ m, ξ m • curlrCoeff ℓ d r m) *ᵥ P = 0) (k : Fin ℓ) (α : Fin r → Fin d)
    (h : Fin r) (i j : Fin d) :
    ξ j * P (k, Function.update α h i) = ξ i * P (k, Function.update α h j) := by
  have := congrFun hP (k, α, h, i, j)
  rw [curlrCoeff_symbol_mulVec] at this
  exact sub_eq_zero.1 this

/-- `P(k,α) ∏_t ξ_{β_t} = P(k,β) ∏_t ξ_{α_t}`. -/
theorem curlr_cone_interp {ξ : Vec d} {P : CurlrCol ℓ d r → ℝ}
    (hP : (∑ m, ξ m • curlrCoeff ℓ d r m) *ᵥ P = 0) (k : Fin ℓ) (α β : Fin r → Fin d) :
    P (k, α) * ∏ t, ξ (β t) = P (k, β) * ∏ t, ξ (α t) := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℕ → Fin r → Fin d,
      ∀ s t, γ s t = if t.val < s then β t else α t := ⟨_, fun _ _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Fin r → ℝ,
      ∀ s t, f s t = if t.val < s then ξ (α t) else ξ (β t) := ⟨_, fun _ _ => rfl⟩
  have step : ∀ s, s < r →
      P (k, γ s) * ∏ t, f s t = P (k, γ (s + 1)) * ∏ t, f (s + 1) t := by
    intro s hs
    set h : Fin r := ⟨s, hs⟩ with hh
    have g1 : γ s = Function.update (γ s) h (α h) := by
      funext t
      by_cases ht : t = h
      · subst ht; simp [hγ, hh]
      · rw [Function.update_of_ne ht]
    have g2 : γ (s + 1) = Function.update (γ s) h (β h) := by
      funext t
      by_cases ht : t = h
      · subst ht; simp [hγ, hh]
      · have : t.val ≠ s := fun e => ht (Fin.ext e)
        rw [Function.update_of_ne ht, hγ, hγ]
        have : (t.val < s + 1) ↔ t.val < s := by omega
        simp [this]
    have hrel := curlr_symbol_relation hP k (γ s) h (α h) (β h)
    rw [← g1, ← g2] at hrel
    have p1 : ∏ t, f s t = ξ (β h) * ∏ t ∈ Finset.univ.erase h, f s t := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ h), hf]
      simp [hh]
    have p2 : ∏ t, f (s + 1) t = ξ (α h) * ∏ t ∈ Finset.univ.erase h, f s t := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ h), hf]
      congr 1
      · simp [hh]
      · refine Finset.prod_congr rfl fun t ht => ?_
        have : t.val ≠ s := fun e => (Finset.mem_erase.1 ht).1 (Fin.ext e)
        have : (t.val < s + 1) ↔ t.val < s := by omega
        simp [hf, this]
    rw [p1, p2]
    calc P (k, γ s) * (ξ (β h) * ∏ t ∈ Finset.univ.erase h, f s t)
        = (ξ (β h) * P (k, γ s)) * ∏ t ∈ Finset.univ.erase h, f s t := by ring
      _ = (ξ (α h) * P (k, γ (s + 1))) * ∏ t ∈ Finset.univ.erase h, f s t := by rw [hrel]
      _ = _ := by ring
  have chain : ∀ s, s ≤ r → P (k, γ 0) * ∏ t, f 0 t = P (k, γ s) * ∏ t, f s t := by
    intro s
    induction s with
    | zero => intro _; rfl
    | succ s ih => intro hs; exact (ih (by omega)).trans (step s (by omega))
  have := chain r le_rfl
  have e0 : γ 0 = α := by funext t; simp [hγ]
  have er : γ r = β := by funext t; simp [hγ, t.isLt]
  have f0 : ∀ t, f 0 t = ξ (β t) := fun t => by simp [hf]
  have fr : ∀ t, f r t = ξ (α t) := fun t => by simp [hf, t.isLt]
  simpa [e0, er, f0, fr] using this

/-- `Σ_β ∏_t ξ_{β_t}² = (Σ_j ξ_j²)^r` (`Finset.prod_univ_sum`). -/
theorem sum_prod_sq_eq (ξ : Vec d) :
    ∑ β : Fin r → Fin d, ∏ t, ξ (β t) * ξ (β t) = (∑ j, ξ j * ξ j) ^ r := by
  have := Finset.prod_univ_sum (fun _ : Fin r => (Finset.univ : Finset (Fin d)))
    (fun _ j => ξ j * ξ j)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp

/-- With `a_k = Σ_β P(k,β) ∏_t ξ_{β_t}` and `Σ_j ξ_j² = 1` we get
`P(k,α) = a_k ∏_t ξ_{α_t}`. -/
theorem curlr_cone_define_a {ξ : Vec d} (hξ : ∑ j, ξ j * ξ j = 1) {P : CurlrCol ℓ d r → ℝ}
    (hP : (∑ m, ξ m • curlrCoeff ℓ d r m) *ᵥ P = 0) (k : Fin ℓ) (α : Fin r → Fin d) :
    P (k, α) = (∑ β : Fin r → Fin d, P (k, β) * ∏ t, ξ (β t)) * ∏ t, ξ (α t) := by
  calc P (k, α) = P (k, α) * ∑ β : Fin r → Fin d, ∏ t, ξ (β t) * ξ (β t) := by
        rw [sum_prod_sq_eq, hξ]; simp
    _ = ∑ β : Fin r → Fin d, (P (k, α) * ∏ t, ξ (β t)) * ∏ t, ξ (β t) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ = ∑ β : Fin r → Fin d, (P (k, β) * ∏ t, ξ (α t)) * ∏ t, ξ (β t) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [curlr_cone_interp hP k α β]
    _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun β _ => ?_
        ring

/-- If `Σ_j ξ_j² = 1` and `(Σ_m ξ_m A_m) P = 0`, then `P(k,α) = a_k ∏_t ξ_{α_t}`
for some `a ∈ ℝ^ℓ`. No symmetry of `P` is assumed. -/
theorem curlr_cone {ξ : Vec d} (hξ : ∑ j, ξ j * ξ j = 1) {P : CurlrCol ℓ d r → ℝ}
    (hP : (∑ m, ξ m • curlrCoeff ℓ d r m) *ᵥ P = 0) :
    ∃ a : Vec ℓ, ∀ (k : Fin ℓ) (α : Fin r → Fin d), P (k, α) = a k * ∏ t, ξ (α t) :=
  ⟨fun k => ∑ β : Fin r → Fin d, P (k, β) * ∏ t, ξ (β t), fun k α =>
    curlr_cone_define_a hξ hP k α⟩

end AFree
