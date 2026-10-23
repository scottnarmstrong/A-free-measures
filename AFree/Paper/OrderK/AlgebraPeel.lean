module

public import AFree.Paper.OrderK.AlgebraDeriv

/-!
# Peeling one coordinate off `∂^α`, and the one-variable Leibniz rules

`∂^α f = D_i^{α_i} ∂^{α with α_i := 0} f` on `U` for smooth `f` (the coordinate peeling formula),
the iterated one-variable Leibniz rule and the one-variable reverse Leibniz rule.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

noncomputable section

variable {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}

/-- The foldr formula defining `multiCoordDeriv`, over an arbitrary list of coordinates. -/
def foldDeriv (l : List (Fin d)) (α : Fin d → ℕ) (f : Vec d → ℝ) : Vec d → ℝ :=
  l.foldr (fun i g => (euclideanCoordDeriv i)^[α i] g) f

theorem multiCoordDeriv_eq_foldDeriv (α : Fin d → ℕ) (f : Vec d → ℝ) :
    multiCoordDeriv α f = foldDeriv (List.finRange d) α f := rfl

theorem foldDeriv_update_of_notMem {l : List (Fin d)} {i : Fin d} (hi : i ∉ l) (α : Fin d → ℕ)
    (n : ℕ) (f : Vec d → ℝ) : foldDeriv l (Function.update α i n) f = foldDeriv l α f := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hj : j ≠ i := fun h => hi (h ▸ List.mem_cons_self)
    have hl : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    simp only [foldDeriv, List.foldr_cons, Function.update_of_ne hj] at ih ⊢
    rw [ih hl]

theorem iterD_comm (hU : IsOpen U) (hf : SmOn U f) (i j : Fin d) (n : ℕ) :
    Set.EqOn (euclideanCoordDeriv j ((euclideanCoordDeriv i)^[n] f))
      ((euclideanCoordDeriv i)^[n] (euclideanCoordDeriv j f)) U := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [D_comm (hf.iterD i n) j i hx]
    exact eqOn_D hU ih i hx

theorem iterD_iterD_comm (hU : IsOpen U) (hf : SmOn U f) (i j : Fin d) (n m : ℕ) :
    Set.EqOn ((euclideanCoordDeriv j)^[m] ((euclideanCoordDeriv i)^[n] f))
      ((euclideanCoordDeriv i)^[n] ((euclideanCoordDeriv j)^[m] f)) U := by
  induction m with
  | zero => exact fun _ _ => rfl
  | succ m ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [eqOn_D hU ih j hx]
    exact iterD_comm hU (hf.iterD j m) i j n hx

theorem foldDeriv_peel (hU : IsOpen U) (hf : SmOn U f) {l : List (Fin d)} (hl : l.Nodup)
    {i : Fin d} (hi : i ∈ l) (α : Fin d → ℕ) :
    Set.EqOn (foldDeriv l α f)
      ((euclideanCoordDeriv i)^[α i] (foldDeriv l (Function.update α i 0) f)) U := by
  induction l with
  | nil => exact absurd hi (by simp)
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    by_cases hji : j = i
    · subst hji
      have h1 : foldDeriv (j :: l) (Function.update α j 0) f = foldDeriv l α f := by
        simp only [foldDeriv, List.foldr_cons, Function.update_self, Function.iterate_zero, id_eq]
        exact foldDeriv_update_of_notMem hl.1 α 0 f
      rw [h1]
      exact fun _ _ => rfl
    · have hi' : i ∈ l := (List.mem_cons.1 hi).resolve_left (Ne.symm hji)
      have ih' := ih hl.2 hi'
      have h1 : foldDeriv (j :: l) (Function.update α i 0) f =
          (euclideanCoordDeriv j)^[α j] (foldDeriv l (Function.update α i 0) f) := by
        simp only [foldDeriv, List.foldr_cons, Function.update_of_ne hji]
      intro x hx
      rw [h1]
      show (euclideanCoordDeriv j)^[α j] (foldDeriv l α f) x = _
      rw [eqOn_iterD hU ih' j (α j) hx]
      exact iterD_iterD_comm hU (hf.foldr (Function.update α i 0) l) i j (α i) (α j) hx

/-- Peeling a coordinate: `∂^α f = D_i^{α_i} ∂^{α_{i↦0}} f`. -/
theorem multiCoordDeriv_peel (hU : IsOpen U) (hf : SmOn U f) (i : Fin d) (α : Fin d → ℕ) :
    Set.EqOn (multiCoordDeriv α f)
      ((euclideanCoordDeriv i)^[α i] (multiCoordDeriv (Function.update α i 0) f)) U :=
  foldDeriv_peel hU hf (List.nodup_finRange d) (List.mem_finRange i) α

theorem multiCoordDeriv_update (hU : IsOpen U) (hf : SmOn U f) (i : Fin d) {β : Fin d → ℕ}
    (hβ : β i = 0) (n : ℕ) :
    Set.EqOn (multiCoordDeriv (Function.update β i n) f)
      ((euclideanCoordDeriv i)^[n] (multiCoordDeriv β f)) U := by
  have h := multiCoordDeriv_peel hU hf i (Function.update β i n)
  have e : Function.update (Function.update β i n) i 0 = β := by
    rw [Function.update_idem]; exact Function.update_eq_self_iff.2 hβ.symm
  rw [e, Function.update_self] at h
  exact h

theorem multiCoordDeriv_zero (f : Vec d → ℝ) : multiCoordDeriv (0 : Fin d → ℕ) f = f := by
  unfold multiCoordDeriv
  induction (List.finRange d) with
  | nil => rfl
  | cons i l ih => simp

/-! ### Iterated derivatives of sums and constant multiples -/

theorem iterD_sum {ι : Type*} (hU : IsOpen U) (s : Finset ι) {F : ι → Vec d → ℝ}
    (h : ∀ a ∈ s, SmOn U (F a)) (i : Fin d) (n : ℕ) :
    Set.EqOn ((euclideanCoordDeriv i)^[n] (fun x => ∑ a ∈ s, F a x))
      (fun x => ∑ a ∈ s, (euclideanCoordDeriv i)^[n] (F a) x) U := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    simp only [Function.iterate_succ_apply']
    rw [eqOn_D hU ih i hx]
    exact D_sum s (fun a ha => (h a ha).iterD i n) i hx

theorem iterD_const_mul (hU : IsOpen U) (c : ℝ) (hf : SmOn U f) (i : Fin d) (n : ℕ) :
    Set.EqOn ((euclideanCoordDeriv i)^[n] (fun x => c * f x))
      (fun x => c * (euclideanCoordDeriv i)^[n] f x) U := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro x hx
    simp only [Function.iterate_succ_apply']
    rw [eqOn_D hU ih i hx]
    exact D_const_mul c (hf.iterD i n) i hx

/-- One-variable iterated Leibniz rule. -/
theorem iterD_mul (hU : IsOpen U) (hf : SmOn U f) (hg : SmOn U g) (i : Fin d) (n : ℕ) :
    Set.EqOn ((euclideanCoordDeriv i)^[n] (fun x => f x * g x))
      (fun x => ∑ ij ∈ Finset.antidiagonal n, (n.choose ij.1 : ℝ) *
        ((euclideanCoordDeriv i)^[ij.1] f x * (euclideanCoordDeriv i)^[ij.2] g x)) U := by
  induction n with
  | zero => intro x hx; simp
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply', eqOn_D hU ih i hx]
    dsimp only
    have hs : ∀ ij ∈ Finset.antidiagonal n, SmOn U (fun x => (n.choose ij.1 : ℝ) *
        ((euclideanCoordDeriv i)^[ij.1] f x * (euclideanCoordDeriv i)^[ij.2] g x)) :=
      fun ij _ => ((hf.iterD i _).mul (hg.iterD i _)).const_mul _
    rw [D_sum _ hs i hx]
    dsimp only
    have hterm : ∀ ij ∈ Finset.antidiagonal n,
        euclideanCoordDeriv i (fun x => (n.choose ij.1 : ℝ) *
          ((euclideanCoordDeriv i)^[ij.1] f x * (euclideanCoordDeriv i)^[ij.2] g x)) x =
        (n.choose ij.1 : ℝ) * ((euclideanCoordDeriv i)^[ij.1] f x *
            (euclideanCoordDeriv i)^[ij.2 + 1] g x) +
        (n.choose ij.2 : ℝ) * ((euclideanCoordDeriv i)^[ij.1 + 1] f x *
            (euclideanCoordDeriv i)^[ij.2] g x) := by
      intro ij hij
      rw [Finset.mem_antidiagonal] at hij
      have e1 := D_const_mul (n.choose ij.1 : ℝ) ((hf.iterD i ij.1).mul (hg.iterD i ij.2)) i hx
      have e2 := D_mul (hf.iterD i ij.1) (hg.iterD i ij.2) i hx
      dsimp only at e1 e2
      rw [e1, e2]
      have : n.choose ij.2 = n.choose ij.1 := Nat.choose_symm_of_eq_add (by omega)
      rw [this]
      simp only [Function.iterate_succ_apply']
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    have := Finset.sum_antidiagonal_choose_succ_mul (R := ℝ)
      (fun a b => (euclideanCoordDeriv i)^[a] f x * (euclideanCoordDeriv i)^[b] g x) n
    rw [this]

/-- Range form of the one-variable Leibniz rule. -/
theorem iterD_mul_range (hU : IsOpen U) (hf : SmOn U f) (hg : SmOn U g) (i : Fin d) (n : ℕ) :
    Set.EqOn ((euclideanCoordDeriv i)^[n] (fun x => f x * g x))
      (fun x => ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
        ((euclideanCoordDeriv i)^[a] f x * (euclideanCoordDeriv i)^[n - a] g x)) U := by
  intro x hx
  rw [iterD_mul hU hf hg i n hx]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun ij => (n.choose ij.1 : ℝ) *
      ((euclideanCoordDeriv i)^[ij.1] f x * (euclideanCoordDeriv i)^[ij.2] g x)) n

/-- One-variable reverse Leibniz rule: `χ D^n g = Σ_{a+b=n} (-1)^b C(n,a) D^a((D^b χ) g)`. -/
theorem iterD_rev (hU : IsOpen U) (hg : SmOn U g) (i : Fin d) (n : ℕ) :
    ∀ {χ : Vec d → ℝ}, SmOn U χ →
    Set.EqOn (fun x => χ x * (euclideanCoordDeriv i)^[n] g x)
      (fun x => ∑ ab ∈ Finset.antidiagonal n, (-1 : ℝ) ^ ab.2 * (n.choose ab.1 : ℝ) *
        (euclideanCoordDeriv i)^[ab.1] (fun y => (euclideanCoordDeriv i)^[ab.2] χ y * g y) x) U := by
  induction n with
  | zero => intro χ _ x hx; simp
  | succ n ih =>
    intro χ hχ x hx
    beta_reduce
    -- χ D^{n+1} g = D(χ D^n g) - (D χ) D^n g
    have hprod := D_mul hχ (hg.iterD i n) i hx
    have h1 : χ x * (euclideanCoordDeriv i)^[n + 1] g x =
        euclideanCoordDeriv i (fun y => χ y * (euclideanCoordDeriv i)^[n] g y) x -
          euclideanCoordDeriv i χ x * (euclideanCoordDeriv i)^[n] g x := by
      rw [hprod, Function.iterate_succ_apply']; ring
    rw [h1, eqOn_D hU (ih hχ) i hx]
    try dsimp only
    have hs : ∀ ab ∈ Finset.antidiagonal n, SmOn U (fun x => (-1 : ℝ) ^ ab.2 * (n.choose ab.1 : ℝ) *
        (euclideanCoordDeriv i)^[ab.1] (fun y => (euclideanCoordDeriv i)^[ab.2] χ y * g y) x) :=
      fun ab _ => (((hχ.iterD i ab.2).mul hg).iterD i ab.1).const_mul _
    rw [D_sum _ hs i hx]
    try dsimp only
    have ihD := ih (hχ.D i) hx
    beta_reduce at ihD
    rw [ihD]
    try dsimp only
    have hterm : ∀ ab ∈ Finset.antidiagonal n,
        euclideanCoordDeriv i (fun x => (-1 : ℝ) ^ ab.2 * (n.choose ab.1 : ℝ) *
          (euclideanCoordDeriv i)^[ab.1] (fun y => (euclideanCoordDeriv i)^[ab.2] χ y * g y) x) x =
        (n.choose ab.1 : ℝ) * ((-1 : ℝ) ^ ab.2 *
          (euclideanCoordDeriv i)^[ab.1 + 1] (fun y => (euclideanCoordDeriv i)^[ab.2] χ y * g y) x) := by
      intro ab _
      have := D_const_mul ((-1 : ℝ) ^ ab.2 * (n.choose ab.1 : ℝ))
        (((hχ.iterD i ab.2).mul hg).iterD i ab.1) i hx
      simp only [] at this
      rw [this, Function.iterate_succ_apply']
      ring
    rw [Finset.sum_congr rfl hterm]
    have hterm2 : ∀ ab ∈ Finset.antidiagonal n,
        (-1 : ℝ) ^ ab.2 * (n.choose ab.1 : ℝ) *
          (euclideanCoordDeriv i)^[ab.1] (fun y => (euclideanCoordDeriv i)^[ab.2]
            (euclideanCoordDeriv i χ) y * g y) x =
        -((n.choose ab.1 : ℝ) * ((-1 : ℝ) ^ (ab.2 + 1) *
          (euclideanCoordDeriv i)^[ab.1] (fun y => (euclideanCoordDeriv i)^[ab.2 + 1] χ y * g y) x)) := by
      intro ab _
      simp only [Function.iterate_succ_apply]
      ring
    rw [Finset.sum_congr rfl hterm2, Finset.sum_neg_distrib, sub_neg_eq_add]
    have := Finset.sum_antidiagonal_choose_succ_mul (R := ℝ)
      (fun a b => (-1 : ℝ) ^ b *
        (euclideanCoordDeriv i)^[a] (fun y => (euclideanCoordDeriv i)^[b] χ y * g y) x) (n)
    have h2 : ∀ ab ∈ Finset.antidiagonal n, (n.choose ab.2 : ℝ) *
        ((-1 : ℝ) ^ ab.2 * (euclideanCoordDeriv i)^[ab.1 + 1]
          (fun y => (euclideanCoordDeriv i)^[ab.2] χ y * g y) x) =
        (n.choose ab.1 : ℝ) * ((-1 : ℝ) ^ ab.2 * (euclideanCoordDeriv i)^[ab.1 + 1]
          (fun y => (euclideanCoordDeriv i)^[ab.2] χ y * g y) x) := by
      intro ab hab
      rw [Finset.mem_antidiagonal] at hab
      rw [Nat.choose_symm_of_eq_add hab.symm]
    rw [Finset.sum_congr rfl h2] at this
    have e : ∑ ij ∈ Finset.antidiagonal (n + 1), (-1 : ℝ) ^ ij.2 * ((n + 1).choose ij.1 : ℝ) *
        (euclideanCoordDeriv i)^[ij.1] (fun y => (euclideanCoordDeriv i)^[ij.2] χ y * g y) x =
        ∑ ij ∈ Finset.antidiagonal (n + 1), ((n + 1).choose ij.1 : ℝ) * ((-1 : ℝ) ^ ij.2 *
        (euclideanCoordDeriv i)^[ij.1] (fun y => (euclideanCoordDeriv i)^[ij.2] χ y * g y) x) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [e, this, add_comm]

end

end AFree
