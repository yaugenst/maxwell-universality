import Maxwell.Continuum.FiniteAuxiliaryOperator
import Maxwell.Continuum.FiniteAuxiliaryBaseline
import Maxwell.Continuum.FiniteAuxiliaryRows
import Maxwell.Continuum.FiniteAuxiliarySeparation
import Maxwell.Continuum.FiniteAuxiliaryNorms

/-! Exact diagonal/off-site decomposition of the physical auxiliary matrix. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Bloch EffectiveMass Auxiliary MasterConstants

attribute [local irreducible] realMode Sh muH

theorem latticeOneNorm_eq_zero_iff (a : Bloch.Alias) : latticeOneNorm a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    funext j
    apply Int.natAbs_eq_zero.mp
    have hj := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      Nat.zero_le (a i).natAbs) (Finset.mem_univ j)
    change (a j).natAbs ≤ latticeOneNorm a at hj
    omega
  · rintro rfl
    simp only [latticeOneNorm, Pi.zero_apply, Int.natAbs_zero, Finset.sum_const_zero]

variable {ι : Type*} [Fintype ι]

def onsiteShift {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (v : ι → ℝ) : DefectSpace ι →L[ℂ] DefectSpace ι :=
  diagonal (fun i => (v i)⁻¹-muH D hh)

def offsite {L : ℕ} {z : ℝ} (D : Calibration (L : ℝ)⁻¹ z)
    (d : ℕ) (position : ι → Bloch.Alias) : DefectSpace ι →L[ℂ] DefectSpace ι :=
  blockOperator (shellBlocks D le_rfl (by positivity) d position 1)

theorem compressed_zero_decomposition {L : ℕ} {z : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (d : ℕ) (position : ι → Bloch.Alias)
    (hinj : Function.Injective position) :
    compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D le_rfl (by positivity)) =
      diagonalBlocks (fun _ : ι => Sh D)+offsite D d position := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  rw [compressed_apply]
  simp only [add_apply, PiLp.add_apply, diagonalBlocks_apply, offsite, blockOperator_apply]
  change (∑ j, interactionBlock (L : ℝ)⁻¹ (centers L d position)
    (resolvent D le_rfl (by positivity)) i j (f j)) = Sh D (f i)+
      ∑ j, shellBlocks D le_rfl (by positivity) d position 1 i j (f j)
  calc
    _ = ∑ j, ((if i = j then Sh D (f i) else 0)+
        shellBlocks D le_rfl (by positivity) d position 1 i j (f j)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp [interactionBlock, centers, site_interaction_diagonal, shellBlocks, latticeOneNorm]
      · have hd : 1 ≤ latticeOneNorm (position i-position j) := by
          have hn : latticeOneNorm (position i-position j) ≠ 0 := by
            intro hz
            exact hij (hinj (sub_eq_zero.mp ((latticeOneNorm_eq_zero_iff _).mp hz)))
          omega
        rw [ite_eq_right hij]
        simp only [zero_add, shellBlocks, ite_eq_left hd]
        exact congrArg (fun A : FieldL2 →L[ℂ] FieldL2 => A (f j))
          (centers_interaction D le_rfl (by positivity) d position i j)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem auxiliaryMatrix_decomposition {L : ℕ} {z σ : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ) :
    auxiliaryMatrix D hσ0 hσ (centers L d position) v =
      baseline D hh+onsiteShift D hh v-offsite D d position-
        (compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D hσ0 hσ)-
          compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D le_rfl (by positivity))) := by
  rw [compressed_zero_decomposition D d position hinj]
  have hb : baseline D hh+onsiteShift D hh v =
      diagonal (fun i => (v i)⁻¹)-diagonalBlocks (fun _ : ι => Sh D) := by
    apply ContinuousLinearMap.ext
    intro f
    apply PiLp.ext
    intro i
    simp only [add_apply, sub_apply, PiLp.add_apply, PiLp.sub_apply]
    change (muH D hh : ℂ) • f i-Sh D (f i)+(((v i)⁻¹-muH D hh : ℝ) : ℂ) • f i =
      (((v i)⁻¹ : ℝ) : ℂ) • f i-Sh D (f i)
    rw [Complex.ofReal_sub, sub_smul]
    abel
  rw [hb, auxiliaryMatrix]
  abel

theorem auxiliaryMatrix_perturbation_bound {L d : ℕ} {z σ c : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ)
    (hc : 0 ≤ c) (hv : ∀ i, |(v i)⁻¹-muH D hh| ≤ c) :
    ‖auxiliaryMatrix D hσ0 hσ (centers L d position) v-baseline D hh‖ ≤
      c+Cs*(L : ℝ)^5*(64*((3 : ℝ)^d)⁻¹+(Fintype.card ι : ℝ)*Real.exp (-cs*(L : ℝ)))+
        16*σ*((L : ℝ)⁻¹^4)⁻¹ := by
  have hs : ‖onsiteShift D hh v‖ ≤ c := diagonal_norm_le _ hc hv
  have ho := offsite_operator_norm hL D le_rfl (by positivity) hd position hinj
  have hdisj : Pairwise fun i j => Disjoint
      (Metric.ball (centers L d position i) ((L : ℝ)⁻¹)⁻¹)
      (Metric.ball (centers L d position j) ((L : ℝ)⁻¹)⁻¹) := by
    simpa only [inv_inv] using centers_disjoint (inv_pos.mp D.h_pos) hd position hinj
  have ht := compressed_detuning D hσ0 hσ (centers L d position) hdisj
  rw [auxiliaryMatrix_decomposition D hh hσ0 hσ d position hinj v]
  have he : baseline D hh+onsiteShift D hh v-offsite D d position-
      (compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D hσ0 hσ)-
        compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D le_rfl (by positivity)))-
      baseline D hh = onsiteShift D hh v-offsite D d position-
      (compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D hσ0 hσ)-
        compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D le_rfl (by positivity))) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hs ho)) ht)

#print axioms compressed_zero_decomposition
#print axioms auxiliaryMatrix_perturbation_bound

end Maxwell.Continuum.FiniteAuxiliary
