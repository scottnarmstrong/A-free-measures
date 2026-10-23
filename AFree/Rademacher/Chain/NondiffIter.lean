module

public import AFree.Rademacher.Chain.PertMain
public import AFree.Rademacher.Robust

/-!
# The explicit iteration for non-differentiability

Step 2 of the proof of non-differentiability: an explicit iteration replacing the Baire category argument in the proof of [AM, Proposition 4.2]. The scalar `c_j` encodes `ε_j = 2^{-j} c_j`, `c_{j+1} = min {c_j, 2^j η_j / 4}`.
-/

@[expose] public section

open PDE MeasureTheory Filter Topology Set
open scoped ENNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- Dependent choice for a step relation. -/
theorem exists_seq_of_step {α : Type*} (P : ℕ → α → Prop) (R : ℕ → α → α → Prop) (a0 : α)
    (h0 : P 0 a0) (hstep : ∀ n a, P n a → ∃ b, P (n + 1) b ∧ R n a b) :
    ∃ a : ℕ → α, a 0 = a0 ∧ (∀ n, P n (a n)) ∧ ∀ n, R n (a n) (a (n + 1)) := by
  classical
  have : Nonempty α := ⟨a0⟩
  choose! next hnext using hstep
  let a : ℕ → α := fun n => Nat.rec a0 (fun n x => next n x) n
  have hP : ∀ n, P n (a n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact (hnext n (a n) ih).1
  exact ⟨a, rfl, hP, fun n => (hnext n (a n) (hP n)).2⟩

/-- The state of the iteration: `(f_j, c_j, K_{j-1})`. -/
abbrev IterState (d : ℕ) := (Vec d → ℝ) × ℝ × Set (Vec d)

/-- The iteration of Step 2, as a sequence with its properties. -/
theorem nondiff_iteration {μ : Measure (Vec d)} {V : Vec d → Submodule ℝ (Vec d)} {i : Fin d}
    {m : ℕ} {δ : ℝ} {E : Set (Vec d)} {e : Vec d → Fin d → Vec d}
    (hS : Setting μ V i m δ E e) :
    ∃ (f : ℕ → Vec d → ℝ) (K : ℕ → Set (Vec d)) (η : ℕ → ℝ) (c : ℕ → ℝ),
      (∀ n, f n ∈ X0 e) ∧ (∀ n, 0 < c n ∧ c n ≤ 1) ∧ Antitone c ∧
      (∀ n y, |f (n + 1) y - f n y| ≤ 2 * (1 / 2) ^ n * c n) ∧
      (∀ n, K n ⊆ E ∧ IsCompact (K n) ∧ μ E / (4 * (m : ℝ≥0∞)) ≤ μ (K n)) ∧
      ∀ n, 0 < η n ∧ c (n + 1) ≤ 2 ^ n / 4 * η n ∧
        ∀ g : Vec d → ℝ, IsLipFun g → (∀ y, |g y - f (n + 1) y| ≤ η n) →
          ∀ x ∈ K n, settingD δ m / 2 ≤ dirOsc g (basisVec i) (1 / ((n : ℝ) + 1)) 0 x := by
  have hD := hS.settingD_pos
  let P : ℕ → IterState d → Prop := fun _ a => a.1 ∈ X0 e ∧ 0 < a.2.1 ∧ a.2.1 ≤ 1
  let R : ℕ → IterState d → IterState d → Prop := fun n a b =>
    b.2.1 ≤ a.2.1 ∧ (∀ y, |b.1 y - a.1 y| ≤ 2 * (1 / 2) ^ n * a.2.1) ∧ b.2.2 ⊆ E ∧
      IsCompact b.2.2 ∧ μ E / (4 * (m : ℝ≥0∞)) ≤ μ b.2.2 ∧
      ∃ η : ℝ, 0 < η ∧ b.2.1 ≤ 2 ^ n / 4 * η ∧
        ∀ g : Vec d → ℝ, IsLipFun g → (∀ y, |g y - b.1 y| ≤ η) →
          ∀ x ∈ b.2.2, settingD δ m / 2 ≤ dirOsc g (basisVec i) (1 / ((n : ℝ) + 1)) 0 x
  have h0 : P 0 ((fun _ => 0), 1, ∅) := by
    refine ⟨?_, one_pos, le_rfl⟩
    rw [X0_iff_fderiv]
    refine ⟨contDiff_const, ⟨0, fun x => by simp⟩, fun x j => ?_⟩
    simp
  have hstep : ∀ n a, P n a → ∃ b, P (n + 1) b ∧ R n a b := by
    intro n a ⟨hfa, hca, hca1⟩
    have hε : 0 < (1 / 2 : ℝ) ^ n * a.2.1 := by positivity
    have hσ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨f'', hf'', K, hKE, hKc, hclose, hμK, hU⟩ :=
      lem_perturbation hS hfa hε hσ (subset_refl E) hS.compact.isClosed.measurableSet
    obtain ⟨σ', hσ'0, hσ'σ, hrob⟩ := lem_robust hS hf'' hKc hσ hU
    set η := settingD δ m * σ' / 32 with hη
    have hηpos : 0 < η := by positivity
    refine ⟨(f'', min a.2.1 (2 ^ n / 4 * η), K), ⟨hf'', lt_min hca (by positivity),
      (min_le_left _ _).trans hca1⟩, min_le_left _ _, fun y => ?_, hKE, hKc, hμK,
      η, hηpos, min_le_right _ _, fun g hg hgη x hx => hrob g hg hgη x hx⟩
    calc |f'' y - a.1 y| ≤ 2 * ((1 / 2) ^ n * a.2.1) := hclose y
      _ = 2 * (1 / 2) ^ n * a.2.1 := by ring
  obtain ⟨a, -, hP, hR⟩ := exists_seq_of_step P R _ h0 hstep
  have hη : ∀ n, ∃ η : ℝ, 0 < η ∧ (a (n + 1)).2.1 ≤ 2 ^ n / 4 * η ∧
      ∀ g : Vec d → ℝ, IsLipFun g → (∀ y, |g y - (a (n + 1)).1 y| ≤ η) →
        ∀ x ∈ (a (n + 1)).2.2, settingD δ m / 2 ≤
          dirOsc g (basisVec i) (1 / ((n : ℝ) + 1)) 0 x := fun n => (hR n).2.2.2.2.2
  choose η hη using hη
  refine ⟨fun n => (a n).1, fun n => (a (n + 1)).2.2, η, fun n => (a n).2.1,
    fun n => (hP n).1, fun n => ⟨(hP n).2.1, (hP n).2.2⟩,
    antitone_nat_of_succ_le fun n => (hR n).1, fun n y => (hR n).2.1 y,
    fun n => ⟨(hR n).2.2.1, (hR n).2.2.2.1, (hR n).2.2.2.2.1⟩, hη⟩

end AFree.Rademacher
