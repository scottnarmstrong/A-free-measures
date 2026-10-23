module

public import AFree.TopCurrents.Assembly.FlatS

/-!
# Normality of `S_φ` for a test function `φ` (normality in the flat-chain identification)

`S'_m = (-1)^{m+1} ∫ ∂_m φ` on `J_m = Fin d ∖ {m}` is a boundary of `S_φ` (integration by parts).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The densities of the boundary `S'` of `S_φ`. -/
noncomputable def bdH (φ : Vec d → ℝ) : KIdx d (d - 1) → Vec d → ℝ := fun J x =>
  ∑ m : Fin d, if J.1 = Finset.univ.erase m then (-1 : ℝ) ^ ((m : ℕ) + 1) * euclideanCoordDeriv m φ x
    else 0

private lemma integrable_deriv {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Set.univ φ) (m : Fin d) :
    Integrable (euclideanCoordDeriv m φ) volume :=
  (contDiff_euclideanCoordDeriv hφ.1 m).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_euclideanCoordDeriv hφ.2.1 m)

private lemma integrable_bdH {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Set.univ φ) (J : KIdx d (d - 1)) :
    Integrable (bdH φ J) volume := by
  unfold bdH
  refine integrable_finsetSum _ fun m _ => ?_
  split_ifs
  · exact (integrable_deriv hφ m).const_mul _
  · exact integrable_zero _ _ _

private lemma card_filter_lt_erase' (m : Fin d) :
    ((Finset.univ.erase m).filter (· < m)).card = (m : ℕ) := by
  have h : (Finset.univ.erase m).filter (· < m) = Finset.Iio m := by
    ext i; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Iio]
    exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  rw [h, Fin.card_Iio]

private lemma exists_erase {J : KIdx d (d - 1)} (hd : 0 < d) : ∃ m : Fin d, J.1 = Finset.univ.erase m := by
  have hc : J.1ᶜ.card = 1 := by
    rw [Finset.card_compl, J.2]; simp [Fintype.card_fin]; omega
  obtain ⟨m, hm⟩ := Finset.card_eq_one.1 hc
  exact ⟨m, by rw [← Finset.compl_singleton, ← hm, compl_compl]⟩

private lemma measurable_bounded_test {ψ : Vec d → ℝ} (hψ : IsTestFunctionOn Set.univ ψ) :
    Measurable ψ ∧ ∃ C, ∀ x, ‖ψ x‖ ≤ C :=
  ⟨hψ.1.continuous.measurable, hψ.1.continuous.bounded_above_of_compact_support hψ.2.1⟩

private lemma ibp {ψ φ : Vec d → ℝ} (hψ : IsTestFunctionOn Set.univ ψ)
    (hφ : IsTestFunctionOn Set.univ φ) (m : Fin d) :
    ∫ x, ψ x * euclideanCoordDeriv m φ x = -∫ x, euclideanCoordDeriv m ψ x * φ x := by
  have hψ' := contDiff_euclideanCoordDeriv hψ.1 m
  have hφ' := contDiff_euclideanCoordDeriv hφ.1 m
  have hψ'c := hasCompactSupport_euclideanCoordDeriv hψ.2.1 m
  have h1 : Integrable fun x => euclideanCoordDeriv m ψ x * φ x :=
    (hψ'.continuous.mul hφ.1.continuous).integrable_of_hasCompactSupport hψ'c.mul_right
  have h2 : Integrable fun x => ψ x * euclideanCoordDeriv m φ x :=
    (hψ.1.continuous.mul hφ'.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_right
  have h3 : Integrable fun x => ψ x * φ x :=
    (hψ.1.continuous.mul hφ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_right
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := basisVec m) h1 h2 h3
    (fun x _ => (hψ.1.differentiable (by simp)) x) (fun x _ => (hφ.1.differentiable (by simp)) x)

/-- `S_φ` is a normal current: `S'_m = (-1)^{m+1} ∂_m φ 𝓛^d` is its boundary. -/
theorem isBoundaryOn_sMeas {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Set.univ φ) :
    IsBoundaryOn Set.univ (sMeas φ) (vMeas (bdH φ)) := by
  have hφi : Integrable φ volume :=
    hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  refine ⟨by simp, fun ψ hψ J => ?_⟩
  obtain ⟨hψm, C, hC⟩ := measurable_bounded_test hψ
  rw [vMeas_integral (integrable_bdH hφ) hψm hC]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [bdH]
  obtain ⟨m, hm⟩ := exists_erase (J := J) hd
  have hbd : ∀ x, bdH φ J x = (-1 : ℝ) ^ ((m : ℕ) + 1) * euclideanCoordDeriv m φ x := by
    intro x
    unfold bdH
    rw [Finset.sum_eq_single m]
    · simp [hm]
    · intro m' _ hm'
      have : ¬ J.1 = Finset.univ.erase m' := by
        rw [hm]; intro h
        have : m' ∈ Finset.univ.erase m := by simp [hm']
        rw [h] at this; simp at this
      simp [this]
    · simp
  have hfil : Finset.univ.filter (· ∉ J.1) = {m} := by
    ext j; simp [hm, eq_comm]
  have hins : insert m J.1 = Finset.univ := by rw [hm]; exact Finset.insert_erase (Finset.mem_univ m)
  have hcard : (insert m J.1).card = d := by rw [hins]; simp
  simp only [hfil, Finset.sum_singleton, hcard, dite_true]
  have htop : (⟨insert m J.1, hcard⟩ : KIdx d d) = topKIdx d := Subtype.ext hins
  rw [htop]
  have hd' : Measurable (euclideanCoordDeriv m ψ) :=
    (contDiff_euclideanCoordDeriv hψ.1 m).continuous.measurable
  obtain ⟨C', hC'⟩ := (contDiff_euclideanCoordDeriv hψ.1 m).continuous.bounded_above_of_compact_support
    (hasCompactSupport_euclideanCoordDeriv hψ.2.1 m)
  rw [sMeas_integral_top hφi hd' (C := C') (fun x => by simpa using hC' x)]
  have hsgn : insertSign m J.1 = (-1 : ℝ) ^ (m : ℕ) := by
    unfold insertSign; rw [hm, card_filter_lt_erase']
  rw [hsgn]
  simp_rw [hbd, ← mul_assoc, mul_comm (ψ _) ((-1 : ℝ) ^ _), mul_assoc]
  rw [integral_const_mul, ibp hψ hφ m, pow_succ]
  ring

end AFree
