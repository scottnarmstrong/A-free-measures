module

public import AFree.MetricCurrents.AKTaylorBasic

/-!
# Taylor lemma: multilinear expansion lemmas for metric currents
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKTaylor

open PDE AFree

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}

lemma isLipFun_add_const {g : Vec d → ℝ} (hg : IsLipFun g) (c : ℝ) :
    IsLipFun (fun x => g x + c) := by
  obtain ⟨K, hK⟩ := hg
  exact ⟨K, fun x y => by simpa using hK x y⟩

lemma isLipFun_add {f g : Vec d → ℝ} (hf : IsLipFun f) (hg : IsLipFun g) :
    IsLipFun (fun x => f x + g x) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hg
  refine ⟨K + K', fun x y => ?_⟩
  have h1 := hK x y
  have h2 := hK' x y
  have e : f x + g x - (f y + g y) = (f x - f y) + (g x - g y) := by ring
  rw [e]; push_cast
  nlinarith [abs_add_le (f x - f y) (g x - g y)]

/-- Constants can be dropped from every slot (`akbasic_constants` slot by slot). -/
lemma T_add_const (hT : IsMetricCurrent k T) {f : Vec d → ℝ} (hf : IsBddLipFun f)
    {g : Fin k → Vec d → ℝ} (hg : IsLipTuple g) (κ : Fin k → ℝ) :
    T f (fun i x => g i x + κ i) = T f g := by
  classical
  have key : ∀ s : Finset (Fin k),
      T f (fun i x => g i x + (if i ∈ s then κ i else 0)) = T f g := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have hw : IsLipTuple (fun i x => g i x + (if i ∈ s then κ i else 0)) := fun i =>
        isLipFun_add_const (hg i) _
      have h1 := (akbasic_constants hT hf hw j (κ j)).2
      have e : (fun i x => g i x + (if i ∈ insert j s then κ i else 0)) =
          Function.update (fun i x => g i x + (if i ∈ s then κ i else 0)) j
            (fun x => g j x + (if j ∈ s then κ j else 0) + κ j) := by
        funext i x
        by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [hij]
      rw [e, h1, ih]
  have := key Finset.univ
  simpa using this

/-- Multilinear expansion of a slot-wise sum over subsets of slots. -/
lemma T_expand (hT : IsMetricCurrent k T) {f : Vec d → ℝ} (hf : IsBddLipFun f)
    {a b : Fin k → Vec d → ℝ} (ha : IsLipTuple a) (hb : IsLipTuple b) :
    T f (fun i x => a i x + b i x) =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        T f (fun i => if i ∈ S then b i else a i) := by
  classical
  have key : ∀ s : Finset (Fin k), ∀ a : Fin k → Vec d → ℝ, IsLipTuple a →
      T f (fun i x => if i ∈ s then a i x + b i x else a i x) =
        ∑ S ∈ s.powerset, T f (fun i => if i ∈ S then b i else a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro a ha; simp
    | insert j s hj ih =>
      intro a ha
      set w : Fin k → Vec d → ℝ := fun i x => if i ∈ s then a i x + b i x else a i x with hwdef
      have hw : IsLipTuple w := fun i => by
        by_cases hi : i ∈ s
        · simpa [hwdef, hi] using isLipFun_add (ha i) (hb i)
        · simpa [hwdef, hi] using ha i
      have hwj : w j = a j := by funext x; simp [hwdef, hj]
      have e1 : (fun i x => if i ∈ insert j s then a i x + b i x else a i x) =
          Function.update w j ((1 : ℝ) • w j + (1 : ℝ) • b j) := by
        funext i x
        by_cases hij : i = j
        · subst hij; simp [hwj]
        · simp [hij, hwdef]
      have h2 := hT.2.2.2.1 f hf w hw j (b j) (hb j) 1 1
      have e2 : Function.update w j (a j) = w := by rw [← hwj]; exact Function.update_eq_self j w
      set a' : Fin k → Vec d → ℝ := Function.update a j (b j) with ha'
      have ha'l : IsLipTuple a' := fun i => by
        by_cases hij : i = j
        · subst hij; simpa [ha'] using hb i
        · simpa [ha', hij] using ha i
      have e3 : Function.update w j (b j) =
          fun i x => if i ∈ s then a' i x + b i x else a' i x := by
        funext i x
        by_cases hij : i = j
        · subst hij; simp [hj, ha']
        · simp [hij, hwdef, ha']
      rw [e1, h2, e3, ih a' ha'l, show T f w = _ from ih a ha, one_mul, one_mul,
        Finset.sum_powerset_insert hj]
      congr 1
      refine Finset.sum_congr rfl fun S hS => ?_
      congr 1
      funext i
      by_cases hij : i = j
      · subst hij; simp [ha']
      · simp [hij, ha']
  have := key Finset.univ a ha
  simpa using this

/-- Linearity of `T(·, π)` over finite linear combinations in `Lip_b` (linearity of `IsMetricCurrent` in `f`). -/
lemma T_sum_lin (hT : IsMetricCurrent k T) {ι : Type*} (s : Finset ι) {w : ι → Vec d → ℝ}
    (hw : ∀ j ∈ s, IsBddLipFun (w j)) (a : ι → ℝ) {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) :
    T (fun x => ∑ j ∈ s, a j * w j x) π = ∑ j ∈ s, a j * T (w j) π := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hT.2.2.1 π hπ (fun _ => 0) (fun _ => 0) (lipb_const 0) (lipb_const 0) 0 0
 
    simp only [Finset.sum_empty]
    change T (0 : Vec d → ℝ) π = 0
    simpa using this
  | insert j s hj ih =>
    have hw' : ∀ i ∈ s, IsBddLipFun (w i) := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hs : IsBddLipFun (fun x => ∑ i ∈ s, a i * w i x) :=
      lipb_sum s fun i hi => by
        exact lipb_smul (a i) (hw' i hi)
    have := hT.2.2.1 π hπ (w j) (fun x => ∑ i ∈ s, a i * w i x) (hw j (Finset.mem_insert_self j s))
      hs (a j) 1
    have e : (fun x => ∑ i ∈ insert j s, a i * w i x) =
        a j • w j + (1 : ℝ) • (fun x => ∑ i ∈ s, a i * w i x) := by
      funext x; simp [Finset.sum_insert hj]
    rw [e, this, ih hw', Finset.sum_insert hj, one_mul]

end AFree.MetricCurrents.AKTaylor
