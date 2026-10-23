module

public import AFree.Paper.OrderK.HarmonicMultideriv

/-!
# Local first-order calculus for the multi-index algebra

Basic calculus for multi-index derivatives, in the local form
needed by the variable-coefficient blow-up: functions that are smooth only on an open set `U`.
`SmOn U f` says `f` is `C^∞` at every point of `U`; all identities are `EqOn U`.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

noncomputable section

variable {d : ℕ}

/-- `f` is `C^∞` at every point of `U` (for open `U`, `f ∈ C^∞(U)`). -/
def SmOn (U : Set (Vec d)) (f : Vec d → ℝ) : Prop :=
  ∀ x ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) f x

variable {U : Set (Vec d)} {f g : Vec d → ℝ}

theorem smOn_univ_iff : SmOn Set.univ f ↔ ContDiff ℝ (⊤ : ℕ∞) f :=
  ⟨fun h => contDiff_iff_contDiffAt.2 fun x => h x trivial, fun h _ _ => h.contDiffAt⟩

theorem SmOn.mono {V : Set (Vec d)} (h : SmOn U f) (hV : V ⊆ U) : SmOn V f :=
  fun x hx => h x (hV hx)

theorem SmOn.sub (hf : SmOn U f) (hg : SmOn U g) : SmOn U (fun x => f x - g x) :=
  fun x hx => (hf x hx).sub (hg x hx)

theorem SmOn.mul (hf : SmOn U f) (hg : SmOn U g) : SmOn U (fun x => f x * g x) :=
  fun x hx => (hf x hx).mul (hg x hx)

theorem SmOn.const_mul (c : ℝ) (hf : SmOn U f) : SmOn U (fun x => c * f x) :=
  fun x hx => contDiffAt_const.mul (hf x hx)

theorem smOn_const (c : ℝ) : SmOn U (fun _ => c) := fun _ _ => contDiffAt_const

theorem SmOn.D (hf : SmOn U f) (i : Fin d) : SmOn U (euclideanCoordDeriv i f) := by
  intro x hx
  unfold euclideanCoordDeriv
  exact ((hf x hx).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const

theorem SmOn.iterD (hf : SmOn U f) (i : Fin d) (n : ℕ) :
    SmOn U ((euclideanCoordDeriv i)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.D i

theorem SmOn.foldr (hf : SmOn U f) (α : Fin d → ℕ) (l : List (Fin d)) :
    SmOn U (l.foldr (fun i g => (euclideanCoordDeriv i)^[α i] g) f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact ih.iterD i (α i)

theorem SmOn.multi (hf : SmOn U f) (α : Fin d → ℕ) : SmOn U (multiCoordDeriv α f) :=
  hf.foldr α _

theorem differentiableAt_of_smOn (hf : SmOn U f) {x : Vec d} (hx : x ∈ U) :
    DifferentiableAt ℝ f x :=
  (hf x hx).differentiableAt (by simp)

/-- `D_i` only sees `f` near the point. -/
theorem eqOn_D (hU : IsOpen U) (h : Set.EqOn f g U) (i : Fin d) :
    Set.EqOn (euclideanCoordDeriv i f) (euclideanCoordDeriv i g) U := by
  intro x hx
  have : f =ᶠ[nhds x] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h
  unfold euclideanCoordDeriv
  rw [this.fderiv_eq]

theorem eqOn_iterD (hU : IsOpen U) (h : Set.EqOn f g U) (i : Fin d) (n : ℕ) :
    Set.EqOn ((euclideanCoordDeriv i)^[n] f) ((euclideanCoordDeriv i)^[n] g) U := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact eqOn_D hU ih i

theorem eqOn_foldr (hU : IsOpen U) (h : Set.EqOn f g U) (α : Fin d → ℕ) (l : List (Fin d)) :
    Set.EqOn (l.foldr (fun i g => (euclideanCoordDeriv i)^[α i] g) f)
      (l.foldr (fun i g => (euclideanCoordDeriv i)^[α i] g) g) U := by
  induction l with
  | nil => exact h
  | cons i l ih => exact eqOn_iterD hU ih i (α i)

/-- Locality: `∂^α f = ∂^α g` on `U` if `f = g` on the open set `U`. -/
theorem eqOn_multiCoordDeriv (hU : IsOpen U) (h : Set.EqOn f g U) (α : Fin d → ℕ) :
    Set.EqOn (multiCoordDeriv α f) (multiCoordDeriv α g) U :=
  eqOn_foldr hU h α _

theorem D_const_mul (c : ℝ) (hf : SmOn U f) (i : Fin d) :
    Set.EqOn (euclideanCoordDeriv i (fun x => c * f x))
      (fun x => c * euclideanCoordDeriv i f x) U := by
  intro x hx
  unfold euclideanCoordDeriv
  have := fderiv_const_mul (differentiableAt_of_smOn hf hx) c
  simp only [] at this ⊢
  rw [this]
  simp

theorem D_mul (hf : SmOn U f) (hg : SmOn U g) (i : Fin d) :
    Set.EqOn (euclideanCoordDeriv i (fun x => f x * g x))
      (fun x => euclideanCoordDeriv i f x * g x + f x * euclideanCoordDeriv i g x) U := by
  intro x hx
  unfold euclideanCoordDeriv
  have := fderiv_mul (differentiableAt_of_smOn hf hx) (differentiableAt_of_smOn hg hx)
  rw [show (fun x => f x * g x) = f * g from rfl, this]
  simp [smul_eq_mul]
  ring

theorem D_sum {ι : Type*} (s : Finset ι) {F : ι → Vec d → ℝ} (h : ∀ i ∈ s, SmOn U (F i))
    (i : Fin d) :
    Set.EqOn (euclideanCoordDeriv i (fun x => ∑ a ∈ s, F a x))
      (fun x => ∑ a ∈ s, euclideanCoordDeriv i (F a) x) U := by
  intro x hx
  unfold euclideanCoordDeriv
  have := fderiv_sum (u := s) (A := F) (fun a ha => differentiableAt_of_smOn (h a ha) hx)
  rw [show (fun x => ∑ a ∈ s, F a x) = ∑ a ∈ s, F a from by ext y; simp, this]
  simp

/-- `D_i D_j = D_j D_i` on smooth functions. -/
theorem D_comm (hf : SmOn U f) (i j : Fin d) :
    Set.EqOn (euclideanCoordDeriv i (euclideanCoordDeriv j f))
      (euclideanCoordDeriv j (euclideanCoordDeriv i f)) U := by
  intro x hx
  have hc : ContDiffAt ℝ 2 f x := (hf x hx).of_le (WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hsym := (hc.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField])).eq (basisVec j) (basisVec i)
  have e : ∀ a b : Fin d, euclideanCoordDeriv a (euclideanCoordDeriv b f) x =
      fderiv ℝ (fderiv ℝ f) x (basisVec a) (basisVec b) := by
    intro a b
    unfold euclideanCoordDeriv
    have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      ((hf x hx).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
    have h1 : (fun y => fderiv ℝ f y (basisVec b)) = fun y => (fderiv ℝ f y) (basisVec b) := rfl
    rw [h1, fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  rw [e i j, e j i]
  exact hsym.symm

end

end AFree
