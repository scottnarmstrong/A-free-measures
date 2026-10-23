module

public import AFree.Curves.Bundle.Intersect
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Existence of the decomposability bundle

[AM, Lemma 2.3]: a finite measure has a decomposability bundle, namely a `μ`-a.e. minimal
element of the class `𝒢_μ` of test fields.
-/

@[expose] public section

open Matrix Filter Topology MeasureTheory PDE
open scoped ENNReal unitInterval

namespace AFree.Bundle

variable {d : ℕ} {μ : Measure (Vec d)}

/-- The constant field `⊤` is a Borel subspace field. -/
theorem isBorelSubspaceField_top : IsBorelSubspaceField (fun _ : Vec d => (⊤ : Submodule ℝ (Vec d))) :=
  ⟨fun _ => 1, fun _ _ => measurable_const, fun _ =>
    ⟨transpose_one, mul_one _, by simp [Matrix.toLin'_one]⟩⟩

/-- The constant field `⊤` lies in `𝒢_μ`. -/
theorem isDecompTestField_top (μ : Measure (Vec d)) :
    IsDecompTestField μ (fun _ : Vec d => (⊤ : Submodule ℝ (Vec d))) :=
  ⟨isBorelSubspaceField_top, fun _ _ => Filter.Eventually.of_forall fun _ _ _ _ =>
    Filter.Eventually.of_forall fun _ _ _ _ => Submodule.mem_top⟩

/-- `𝒢_μ` is closed under countable intersection. -/
theorem isDecompTestField_iInf {V : ℕ → Vec d → Submodule ℝ (Vec d)}
    (hV : ∀ n, IsDecompTestField μ (V n)) :
    IsDecompTestField μ (fun x => ⨅ n, V n x) := by
  refine ⟨(borelinter fun n => (hV n).1).1, fun E hE => ?_⟩
  have h1 := ae_all_iff.2 fun n => (hV n).2 E hE
  filter_upwards [h1] with t ht γ J hγ
  have h2 := ae_all_iff.2 fun n => ht n γ J hγ
  filter_upwards [h2] with x hx s hs hsx
  exact Submodule.mem_iInf _ |>.2 fun n => hx n s hs hsx

private theorem iInf_two (A B : Submodule ℝ (Vec d)) :
    (⨅ n : ℕ, if n = 0 then A else B) = A ⊓ B := by
  apply le_antisymm
  · exact le_inf (by simpa using iInf_le (fun n : ℕ => if n = 0 then A else B) 0)
      (by simpa using iInf_le (fun n : ℕ => if n = 0 then A else B) 1)
  · refine le_iInf fun n => ?_
    by_cases h : n = 0
    · simp [h]
    · simp [h]

/-- Binary intersection, from the countable case. -/
theorem isDecompTestField_inf {V W : Vec d → Submodule ℝ (Vec d)}
    (hV : IsDecompTestField μ V) (hW : IsDecompTestField μ W) :
    IsDecompTestField μ (fun x => V x ⊓ W x) := by
  have h := isDecompTestField_iInf (μ := μ) (V := fun n x => if n = 0 then V x else W x) fun n => by
    by_cases h : n = 0
    · simpa [h] using hV
    · simpa [h] using hW
  simpa only [iInf_two] using h

/-- `Φ(V) = ∫ dim V(x) dμ(x)`. -/
noncomputable def dimInt (μ : Measure (Vec d)) (V : Vec d → Submodule ℝ (Vec d)) : ℝ≥0∞ :=
  ∫⁻ x, (Module.finrank ℝ (V x) : ℝ≥0∞) ∂μ

private theorem dimInt_mono {V W : Vec d → Submodule ℝ (Vec d)} (h : ∀ x, V x ≤ W x) :
    dimInt μ V ≤ dimInt μ W :=
  lintegral_mono fun x => Nat.cast_le.2 (Submodule.finrank_mono (h x))

private theorem dimInt_ne_top [IsFiniteMeasure μ] (V : Vec d → Submodule ℝ (Vec d)) :
    dimInt μ V ≠ ⊤ := by
  have : dimInt μ V ≤ ∫⁻ _, (d : ℝ≥0∞) ∂μ := lintegral_mono fun x => by
    have := Submodule.finrank_le (V x)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    exact Nat.cast_le.2 this
  rw [lintegral_const] at this
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (measure_ne_top _ _)) this

/-- [AM, Lemma 2.3]: for a finite measure `μ`, `𝒢_μ` has a
`μ`-a.e. minimal element, and it belongs to `𝒢_μ`. -/
theorem exists_minimal_decompTestField [IsFiniteMeasure μ] :
    ∃ V, IsDecompTestField μ V ∧ ∀ W, IsDecompTestField μ W → ∀ᵐ x ∂μ, V x ≤ W x := by
  set S : Set ℝ≥0∞ := {r | ∃ V, IsDecompTestField μ V ∧ dimInt μ V = r} with hS
  have hne : S.Nonempty := ⟨_, _, isDecompTestField_top μ, rfl⟩
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sInf hne (OrderBot.bddBelow S)
  choose Vj hVj hΦ using huS
  have hG : IsDecompTestField μ (fun x => ⨅ j, Vj j x) := isDecompTestField_iInf hVj
  have hle : dimInt μ (fun x => ⨅ j, Vj j x) ≤ sInf S :=
    ge_of_tendsto' hu fun j => (hΦ j) ▸ dimInt_mono fun x => iInf_le (fun j => Vj j x) j
  refine ⟨fun x => ⨅ j, Vj j x, hG, fun W hW => ?_⟩
  have hG'' := isDecompTestField_inf hG hW
  have h1 : dimInt μ (fun x => (⨅ j, Vj j x) ⊓ W x) = dimInt μ (fun x => ⨅ j, Vj j x) :=
    le_antisymm (dimInt_mono fun x => inf_le_left) (hle.trans (sInf_le ⟨_, hG'', rfl⟩))
  have hmeas := (borelinter fun j => (hVj j).1).2.1
  have hae := ae_eq_of_ae_le_of_lintegral_le (μ := μ)
    (f := fun x => (Module.finrank ℝ ((⨅ j, Vj j x) ⊓ W x : Submodule ℝ (Vec d)) : ℝ≥0∞))
    (g := fun x => (Module.finrank ℝ (⨅ j, Vj j x : Submodule ℝ (Vec d)) : ℝ≥0∞))
    (Filter.Eventually.of_forall fun x => Nat.cast_le.2 (Submodule.finrank_mono inf_le_left))
    (dimInt_ne_top _) ((measurable_from_nat (f := fun n : ℕ => (n : ℝ≥0∞))).comp hmeas).aemeasurable
    h1.ge
  filter_upwards [hae] with x hx
  have hx' : Module.finrank ℝ ((⨅ j, Vj j x) ⊓ W x : Submodule ℝ (Vec d)) =
      Module.finrank ℝ (⨅ j, Vj j x : Submodule ℝ (Vec d)) := by exact_mod_cast hx
  have := Submodule.eq_of_le_of_finrank_eq inf_le_left hx'
  rw [← this]
  exact inf_le_right

/-- [AM, Lemma 2.3]: for every finite measure `μ` on `ℝ^d` there
is `V` with `IsDecompBundle μ V`. -/
theorem bundle_exists (μ : Measure (Vec d)) [IsFiniteMeasure μ] : ∃ V, IsDecompBundle μ V :=
  exists_minimal_decompTestField.imp fun _ h => h

end AFree.Bundle
