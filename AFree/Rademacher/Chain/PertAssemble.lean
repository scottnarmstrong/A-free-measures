module

public import AFree.Rademacher.Chain.PertClaimA
public import AFree.Rademacher.Chain.PertSetup

/-!
# Assembling the disjoint perturbations

Verification step in the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE Filter Topology Set

namespace AFree.Rademacher

variable {d : ℕ}

/-- The data attached to one ball `B̄(p, r)` of the covering: the local data, the cut-off
perturbation `g` with its enlarged radius `r'`, the compact set `K` and the sign `ς`. -/
structure Piece (e : Vec d → Fin d → Vec d) (f : Vec d → ℝ) (v : Vec d) (k : Fin d)
    (q s ω θ ρc σ ε' : ℝ) (p : Vec d) (r r' : ℝ) (g : Vec d → ℝ) (K : Set (Vec d)) (ς : ℝ) :
    Prop where
  ld : LocalData e f p r s ω θ ρc
  cd : CutData e k p r' ε' (6 * ρc) g K
  r_lt : r < r'
  r'_le : r' ≤ 2 * r
  ε_s : ε' ≤ s
  ε_r : ε' ≤ r ^ 2
  r_σ : 4 * r ≤ σ
  r_c : 3 * r ≤ 8 * ρc
  K_sub : K ⊆ Metric.closedBall p r
  K_q : ∀ x ∈ K, q ≤ |vecDot v (e x k)|
  sign : (ς = 1 ∧ fderiv ℝ f p (e p k) ≤ 0) ∨ (ς = -1 ∧ 0 < fderiv ℝ f p (e p k))
  num : ω / 2 + 4 * ρc + 2 * θ ≤ q / 6

theorem Piece.abs_sign {e : Vec d → Fin d → Vec d} {f : Vec d → ℝ} {v : Vec d} {k : Fin d}
    {q s ω θ ρc σ ε' : ℝ} {p : Vec d} {r r' : ℝ} {g : Vec d → ℝ} {K : Set (Vec d)} {ς : ℝ}
    (h : Piece e f v k q s ω θ ρc σ ε' p r r' g K ς) : ς = 1 ∨ ς = -1 := by
  rcases h.sign with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

/-- Assembly: for a finite family of pieces with pairwise
disjoint enlarged balls, `f'' = f' + ∑ ḡ_p` lies in `X₀`, is `ε'/2`-close to `f'`, and
`U_σ f'' ≥ q/3` on every `K p`. -/
theorem pert_assemble {e : Vec d → Fin d → Vec d} {f : Vec d → ℝ} (hf : f ∈ X0 e) (he : IsFrame e)
    {v : Vec d} (hv : vecEuclideanNorm v = 1) {k : Fin d} {q s ω θ ρc σ ε' : ℝ} (hε' : 0 < ε')
    (T : Finset (Vec d)) (r r' : Vec d → ℝ) (g : Vec d → Vec d → ℝ) (K : Vec d → Set (Vec d))
    (ς : Vec d → ℝ)
    (hP : ∀ p ∈ T, Piece e f v k q s ω θ ρc σ ε' p (r p) (r' p) (g p) (K p) (ς p))
    (hdis : ∀ p ∈ T, ∀ p' ∈ T, p ≠ p' →
      Disjoint (Metric.closedBall p (r' p)) (Metric.closedBall p' (r' p'))) :
    (fun y => f y + ∑ p ∈ T, ς p / 2 * g p y) ∈ X0 e ∧
    (∀ y, |∑ p ∈ T, ς p / 2 * g p y| ≤ ε' / 2) ∧
    ∀ p ∈ T, ∀ x ∈ K p, q / 3 ≤ dirOsc (fun y => f y + ∑ p ∈ T, ς p / 2 * g p y) v σ 0 x := by
  obtain ⟨hsm, ⟨C, hC⟩, hD⟩ := X0_iff_fderiv.1 hf
  have hdf : Differentiable ℝ f := hsm.differentiable (by simp)
  have hgs : ∀ p ∈ T, ContDiff ℝ (⊤ : ℕ∞) fun y => ς p / 2 * g p y :=
    fun p hp => contDiff_const.mul (hP p hp).cd.smooth
  have hsupp : ∀ p ∈ T, tsupport (fun y => ς p / 2 * g p y) ⊆ Metric.closedBall p (r' p) :=
    fun p hp => tsupport_mul_subset_right.trans (hP p hp).cd.supp
  obtain ⟨hsum1, hsum0⟩ := sum_disjoint_support T (fun p => Metric.closedBall p (r' p))
    (fun p y => ς p / 2 * g p y) hgs hsupp hdis
  have hςa : ∀ p ∈ T, |ς p / 2| = 1 / 2 := by
    intro p hp
    rcases (hP p hp).abs_sign with h | h <;> simp [h, abs_div]
  have hgp : ∀ p ∈ T, ∀ y, |ς p / 2 * g p y| ≤ ε' / 2 := by
    intro p hp y
    rw [abs_mul, hςa p hp]
    have := (hP p hp).cd.bound y
    linarith
  have hGb : ∀ y, |∑ p ∈ T, ς p / 2 * g p y| ≤ ε' / 2 := by
    intro y
    by_cases hy : ∃ p ∈ T, y ∈ Metric.closedBall p (r' p)
    · obtain ⟨p, hp, hyp⟩ := hy
      rw [(hsum1 p hp y hyp).1]; exact hgp p hp y
    · push Not at hy
      rw [(hsum0 y hy).1, abs_zero]
      linarith
  have hGd : Differentiable ℝ fun y => ∑ p ∈ T, ς p / 2 * g p y :=
    (ContDiff.sum hgs).differentiable (by simp)
  have hFd : ∀ p ∈ T, ∀ x ∈ Metric.closedBall p (r' p), ∀ w,
      fderiv ℝ (fun y => f y + ∑ p ∈ T, ς p / 2 * g p y) x w =
        fderiv ℝ (fun y => f y + ς p / 2 * g p y) x w := by
    intro p hp x hx w
    have hdp : Differentiable ℝ fun y => ς p / 2 * g p y := (hgs p hp).differentiable (by simp)
    rw [fderiv_fun_add (hdf x) (hGd x), fderiv_fun_add (hdf x) (hdp x), (hsum1 p hp x hx).2]
  have hX0 : (fun y => f y + ∑ p ∈ T, ς p / 2 * g p y) ∈ X0 e := by
    rw [X0_iff_fderiv]
    refine ⟨hsm.add (ContDiff.sum hgs), ⟨C + ε' / 2, fun y => ?_⟩, fun x j => ?_⟩
    · calc |f y + ∑ p ∈ T, ς p / 2 * g p y|
          ≤ |f y| + |∑ p ∈ T, ς p / 2 * g p y| := abs_add_le _ _
        _ ≤ C + ε' / 2 := add_le_add (hC y) (hGb y)
    · by_cases hx : ∃ p ∈ T, x ∈ Metric.closedBall p (r' p)
      · obtain ⟨p, hp, hxp⟩ := hx
        rw [hFd p hp x hxp]
        exact pert_claimB (hP p hp).ld (hP p hp).cd (hP p hp).r'_le (hP p hp).ε_s
          (hP p hp).sign x j
      · push Not at hx
        rw [fderiv_fun_add (hdf x) (hGd x), (hsum0 x hx).2]
        simpa using (hD x j)
  refine ⟨hX0, hGb, fun p hp x hxK => ?_⟩
  have hpc := hP p hp
  have hlip : IsLipFun (fun y => f y + ∑ p ∈ T, ς p / 2 * g p y) :=
    ⟨_, (X0_lipschitz he).2.1 _ hX0⟩
  have hdiffx : DifferentiableAt ℝ (fun y => f y + ∑ p ∈ T, ς p / 2 * g p y) x :=
    (hf.1.add (ContDiff.sum hgs)).differentiable (by simp) x |> fun h => by
      simpa using h
  have hr0 := hpc.ld.r_pos
  have hhpos : 0 < 4 * r p := by linarith
  have hxr : ‖x - p‖ ≤ r p := by
    have := Metric.mem_closedBall.1 (hpc.K_sub hxK)
    rwa [dist_eq_norm] at this
  have hxB : x ∈ Metric.closedBall p (r' p) :=
    Metric.closedBall_subset_closedBall hpc.r_lt.le (hpc.K_sub hxK)
  have hvn : ‖v‖ ≤ 1 := (norm_le_vecEuclideanNorm v).trans hv.le
  have hlow := (lem_U hv).2.2.2.2 _ hlip x hdiffx σ (4 * r p) hhpos hpc.r_σ
  refine le_trans ?_ hlow
  have hA := pert_claimA hpc.ld hpc.cd hpc.abs_sign hv hvn hpc.num hpc.r_c hpc.ε_r hxK hxr
    (hpc.K_q x hxK) (a := ∑ q ∈ T, ς q / 2 * g q (x + (4 * r p) • v))
    ((hGb _).trans (by linarith : ε' / 2 ≤ ε'))
  have hG0 : ∑ q ∈ T, ς q / 2 * g q x = ς p / 2 * g p x := (hsum1 p hp x hxB).1
  have hdq : dirQuot (fun y => f y + ∑ p ∈ T, ς p / 2 * g p y) v x (4 * r p) =
      (f (x + (4 * r p) • v) + ∑ q ∈ T, ς q / 2 * g q (x + (4 * r p) • v) -
        (f x + ς p / 2 * g p x)) / (4 * r p) := by
    unfold dirQuot
    simp only [hG0]
  rw [hdq, hFd p hp x hxB]
  exact hA

end AFree.Rademacher
