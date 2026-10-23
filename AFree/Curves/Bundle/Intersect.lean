module

public import AFree.Curves.Bundle.Borel
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Order.OrderIsoNat

/-!
# Borel subspace fields are closed under countable intersection

We use the finite sums `A_N = ∑_{n<N} (I - Pₙ)`: the
projections `Q_N` onto `ker A_N = ⋂_{n<N} Vₙ` are Borel by the resolvent limit, and for every `x`
the decreasing finite-dimensional subspaces `⋂_{n<N} Vₙ(x)` stabilize, so `Q_N(x)` is eventually
constant and its pointwise limit is the (Borel) projection onto `⋂ₙ Vₙ(x)`.
-/

@[expose] public section

open Matrix Filter Topology MeasureTheory PDE

namespace AFree.Bundle

variable {d : ℕ}

/-- For a Borel subspace field `V`, `x ↦ dim V(x)` is Borel
(it is the trace of the projection matrix) and `{x | v ∈ V x}` is Borel for every `v`. -/
theorem dimension_borel {V : Vec d → Submodule ℝ (Vec d)} (hV : IsBorelSubspaceField V) :
    Measurable (fun x => Module.finrank ℝ (V x)) ∧ ∀ v, MeasurableSet {x | v ∈ V x} := by
  obtain ⟨P, hPm, hPp⟩ := hV
  have hP : ∀ x, IsProjMat (P x) (V x) := hPp
  have hPmeas : EntryMeas P := hPm
  refine ⟨?_, fun v => ?_⟩
  · have htr : ∀ x, (Module.finrank ℝ (V x) : ℝ) = (P x).trace := fun x => by
      have hidem : IsIdempotentElem (Matrix.toLin' (P x)) := by
        rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, (hP x).2.1]
      have h := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
      rw [(hP x).2.2] at h
      rw [← h, Matrix.trace_toLin'_eq]
    have hmeas : Measurable fun x => (P x).trace :=
      Finset.measurable_sum _ fun i _ => hPmeas i i
    have heq : (fun x => Module.finrank ℝ (V x)) = fun x => ⌊(P x).trace⌋₊ := by
      funext x
      rw [← htr, Nat.floor_natCast]
    rw [heq]
    exact hmeas.nat_floor
  · have hf : Measurable fun x => P x *ᵥ v := by
      refine measurable_pi_iff.2 fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.measurable_sum _ fun j _ => (hPmeas i j).mul_const _
    have : {x | v ∈ V x} = (fun x => P x *ᵥ v) ⁻¹' {v} := by
      ext x; simp [(hP x).mem_iff v]
    rw [this]
    exact hf (measurableSet_singleton v)

/-- Finite intersections `⋂_{n<N} Vₙ(x)`. -/
private def finInf (V : ℕ → Vec d → Submodule ℝ (Vec d)) (N : ℕ) (x : Vec d) : Submodule ℝ (Vec d) :=
  ⨅ n, ⨅ (_ : n < N), V n x

private theorem finInf_antitone (V : ℕ → Vec d → Submodule ℝ (Vec d)) (x : Vec d) :
    Antitone fun N => finInf V N x := fun N N' h => by
  unfold finInf
  refine le_iInf₂ fun n hn => ?_
  have hn' : n < N' := lt_of_lt_of_le hn h
  exact iInf₂_le (f := fun n (_ : n < N') => V n x) n hn'

private theorem finInf_stabilizes (V : ℕ → Vec d → Submodule ℝ (Vec d)) (x : Vec d) :
    ∃ N₀, (∀ N, N₀ ≤ N → finInf V N x = finInf V N₀ x) ∧
      finInf V N₀ x = ⨅ n, V n x := by
  obtain ⟨N₀, hN₀⟩ := WellFoundedLT.antitone_chain_condition (finInf_antitone V x)
  refine ⟨N₀, fun N hN => (hN₀ N hN).symm, le_antisymm ?_ ?_⟩
  · refine le_iInf fun n => ?_
    have := hN₀ (max N₀ (n + 1)) (le_max_left _ _)
    rw [this]
    unfold finInf
    have hn' : n < max N₀ (n + 1) := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
    exact iInf₂_le (f := fun k (_ : k < max N₀ (n + 1)) => V k x) n hn'
  · unfold finInf
    exact le_iInf fun n => le_iInf fun _ => iInf_le (fun n => V n x) n

/-- If `Vₙ` (`n ∈ ℕ`) are Borel subspace fields, then `V(x) = ⋂ₙ Vₙ(x)` is a
Borel subspace field; moreover `x ↦ dim V(x)` is Borel and `{x | v ∈ V x}` is Borel for every `v`. -/
theorem borelinter {V : ℕ → Vec d → Submodule ℝ (Vec d)} (hV : ∀ n, IsBorelSubspaceField (V n)) :
    IsBorelSubspaceField (fun x => ⨅ n, V n x) ∧
      Measurable (fun x => Module.finrank ℝ (⨅ n, V n x : Submodule ℝ (Vec d))) ∧
      ∀ v, MeasurableSet {x | v ∈ ⨅ n, V n x} := by
  have hmain : IsBorelSubspaceField (fun x => ⨅ n, V n x) := by
    choose P hPm hPp using hV
    have hP : ∀ n x, IsProjMat (P n x) (V n x) := hPp
    have hPe : ∀ n, EntryMeas (P n) := hPm
    let Q : ℕ → Vec d → Matrix (Fin d) (Fin d) ℝ := fun N x => kerProj (wsum (fun n => P n x) N)
    have hQp : ∀ N x, IsProjMat (Q N x) (finInf V N x) := fun N x => by
      obtain ⟨hs, hk⟩ := kernel_of_weighted_sum (fun n => hP n x) N
      obtain ⟨h1, h2, h3⟩ := hs.kerProj_spec
      refine ⟨h1, h2, h3.trans ?_⟩
      ext y
      simp only [LinearMap.mem_ker, Matrix.toLin'_apply, finInf, Submodule.mem_iInf]
      rw [hk y]
    have hQm : ∀ N, EntryMeas (Q N) := fun N =>
      entryMeas_kerProj (entryMeas_wsum hPe N) fun x => (kernel_of_weighted_sum (fun n => hP n x) N).1
    have hlim : ∀ x, ∃ N₀, Tendsto (fun N => Q N x) atTop (𝓝 (Q N₀ x)) ∧
        IsProjMat (Q N₀ x) (⨅ n, V n x) := fun x => by
      obtain ⟨N₀, hst, heq⟩ := finInf_stabilizes V x
      refine ⟨N₀, tendsto_atTop_of_eventually_const (i₀ := N₀) fun N hN => ?_, heq ▸ hQp N₀ x⟩
      exact (hQp N x).unique (hst N hN ▸ hQp N₀ x)
    let Qinf : Vec d → Matrix (Fin d) (Fin d) ℝ := fun x => limUnder atTop fun N => Q N x
    have hQinf : ∀ x, Tendsto (fun N => Q N x) atTop (𝓝 (Qinf x)) ∧
        IsProjMat (Qinf x) (⨅ n, V n x) := fun x => by
      obtain ⟨N₀, ht, hp⟩ := hlim x
      have : Qinf x = Q N₀ x := ht.limUnder_eq
      rw [this]; exact ⟨ht, hp⟩
    refine ⟨Qinf, ?_, fun x => (hQinf x).2⟩
    intro i j
    refine measurable_of_tendsto_metrizable (f := fun N x => Q N x i j) (fun N => hQm N i j) ?_
    rw [tendsto_pi_nhds]
    intro x
    exact (((continuous_apply j).comp (continuous_apply i)).tendsto _).comp (hQinf x).1
  exact ⟨hmain, dimension_borel hmain⟩

end AFree.Bundle
