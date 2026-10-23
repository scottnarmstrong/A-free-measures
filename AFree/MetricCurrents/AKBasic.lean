module

public import AFree.MetricCurrents.AKMass
public import AFree.MetricCurrents.AKExtAux

/-!
# Elementary consequences of the axioms ([AK, Definitions 2.6 and 3.1])
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.AKExt

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}

/-- For `T ∈ M_k(ℝ^d)` the chosen measure `akMassMeasure T` is the mass `μ_T`:
`|T(f,π)| ≤ P(K) ∫ |f| dμ_T`. -/
theorem akMassMeasure_isAKMass (hT : IsMetricCurrent k T) : IsAKMass T (akMassMeasure T) := by
  have H : ∃ μ, IsAKMass T μ := (akmass hT.1 hT.2.1).1
  unfold akMassMeasure
  simp only [H, ↓reduceDIte]
  exact H.choose_spec

/-- (a) `T(f, π[i ↦ 0]) = 0`, and slot `i` is linear over finite
sums of Lipschitz functions. -/
theorem akbasic_slot_linear (hT : IsMetricCurrent k T) {f : Vec d → ℝ} (hf : IsBddLipFun f)
    {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) (i : Fin k) :
    T f (Function.update π i 0) = 0 ∧
    ∀ {ι : Type} (s : Finset ι) (c : ι → ℝ) (ψ : ι → Vec d → ℝ), (∀ l ∈ s, IsLipFun (ψ l)) →
      T f (Function.update π i (∑ l ∈ s, c l • ψ l)) =
        ∑ l ∈ s, c l * T f (Function.update π i (ψ l)) := by
  classical
  obtain ⟨-, -, -, hC2, -, -⟩ := hT
  have h0 : T f (Function.update π i 0) = 0 := by
    have := hC2 f hf π hπ i 0 lip_zero 0 0
    simpa using this
  refine ⟨h0, ?_⟩
  intro ι s c ψ hψ
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS : IsLipFun (∑ l ∈ s, c l • ψ l) := lip_sum s c ψ fun l hl => hψ l (Finset.mem_insert_of_mem hl)
    have hπ' : IsLipTuple (Function.update π i (ψ a)) :=
      lipTuple_update hπ i (hψ a (Finset.mem_insert_self _ _))
    have := hC2 f hf _ hπ' i _ hS (c a) 1
    simp only [Function.update_self, one_smul, one_mul, Function.update_idem] at this
    rw [← ih fun l hl => hψ l (Finset.mem_insert_of_mem hl)]
    exact this

/-- (b) Constants can be dropped: `T(f, π[i ↦ c]) = 0` and
`T(f, π[i ↦ π_i + c]) = T(f, π)`. -/
theorem akbasic_constants (hT : IsMetricCurrent k T) {f : Vec d → ℝ} (hf : IsBddLipFun f)
    {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) (i : Fin k) (c : ℝ) :
    T f (Function.update π i (fun _ => c)) = 0 ∧
    T f (Function.update π i (fun x => π i x + c)) = T f π := by
  obtain ⟨-, -, -, hC2, -, hC4⟩ := hT
  have key : ∀ c : ℝ, T f (Function.update π i (fun _ => c)) = 0 := fun c =>
    hC4 f hf _ (lipTuple_update hπ i (lip_const c)) i
      ⟨Set.univ, isOpen_univ, Set.subset_univ _, c, fun x _ => by simp⟩
  refine ⟨key c, ?_⟩
  have := hC2 f hf π hπ i (fun _ => 1) (lip_const 1) 1 c
  have e : (fun x => π i x + c) = (1 : ℝ) • π i + c • (fun _ : Vec d => (1 : ℝ)) := by
    funext x; simp
  rw [e, this, key 1]
  ring

/-- (c) If `{f ≠ 0} ⊆ U` open and `π_l = π'_l` on `U` for all `l`,
then `T(f, π) = T(f, π')`. -/
theorem akbasic_open_locality (hT : IsMetricCurrent k T) {f : Vec d → ℝ} (hf : IsBddLipFun f)
    {π π' : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) (hπ' : IsLipTuple π') {U : Set (Vec d)}
    (hU : IsOpen U) (hfU : {x | f x ≠ 0} ⊆ U) (heq : ∀ l, ∀ x ∈ U, π l x = π' l x) :
    T f π = T f π' := by
  classical
  obtain ⟨-, -, -, hC2, -, hC4⟩ := hT
  let ρ : Finset (Fin k) → Fin k → Vec d → ℝ := fun s j => if j ∈ s then π' j else π j
  have hρ : ∀ s, IsLipTuple (ρ s) := fun s j => by
    by_cases h : j ∈ s <;> simp [ρ, h, hπ j, hπ' j]
  have claim : ∀ s, T f (ρ s) = T f π := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [ρ]
    | insert l s hl ih =>
      have hup : ρ (insert l s) = Function.update (ρ s) l (π' l) := by
        funext j
        by_cases hj : j = l
        · subst hj; simp [ρ]
        · simp [ρ, hj]
      have hρl : ρ s l = π l := by simp [ρ, hl]
      have hdiff : IsLipFun (fun x => π' l x - π l x) := lip_sub (hπ' l) (hπ l)
      have h2 := hC2 f hf (ρ s) (hρ s) l _ hdiff 1 1
      have e : (1 : ℝ) • ρ s l + (1 : ℝ) • (fun x => π' l x - π l x) = π' l := by
        funext x; simp [hρl]
      rw [e] at h2
      have h3 : T f (Function.update (ρ s) l (fun x => π' l x - π l x)) = 0 :=
        hC4 f hf _ (lipTuple_update (hρ s) l hdiff) l
          ⟨U, hU, hfU, 0, fun x hx => by simp [heq l x hx]⟩
      rw [hup, h2, h3, ih]; ring
  have := claim Finset.univ
  have e : ρ Finset.univ = π' := by funext j; simp [ρ]
  rw [e] at this
  exact this.symm

/-- (d) `|T(f,π) - T(g,π)| ≤ P(K) ∫ |f - g| dμ` for every
admissible `μ` (in particular `μ_T`), `f, g ∈ Lip_b` and `π` `K`-Lipschitz. -/
theorem akbasic_abs_sub_le (hT : IsMetricCurrent k T) {μ : Measure (Vec d)}
    (hμ : IsAKMassAdmissible T μ) {f g : Vec d → ℝ} (hf : IsBddLipFun f) (hg : IsBddLipFun g)
    {π : Fin k → Vec d → ℝ} {K : Fin k → ℝ≥0} (hπ : ∀ i, IsEuclLipschitzWith (K i) (π i)) :
    |T f π - T g π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |f x - g x| ∂μ := by
  obtain ⟨-, -, hC1, -, -, -⟩ := hT
  have hπl : IsLipTuple π := fun i => ⟨K i, hπ i⟩
  have h1 := hC1 π hπl f g hf hg 1 (-1)
  have e : (1 : ℝ) • f + (-1 : ℝ) • g = fun x => f x - g x := by
    funext x; simp [sub_eq_add_neg]
  rw [e] at h1
  have := hμ.2 (fun x => f x - g x) (bddLip_sub hf hg) π K hπ
  rw [show T f π - T g π = T (fun x => f x - g x) π by rw [h1]; ring]
  exact this

end AFree
