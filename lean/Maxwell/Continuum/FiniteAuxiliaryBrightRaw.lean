import Maxwell.Continuum.FiniteAuxiliaryIncidence
import Maxwell.Continuum.FiniteAuxiliaryLogical

/-! Direct bright error for the literal routed continuum assembly:
diagonal rounding, calibrated incidences, all nonneighbors, and detuning. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants Maxwell.Composition

attribute [local irreducible] realMode Sh muH Cs

variable {ι : Type*} [Fintype ι]

def brightMatrix {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι) : BrightSpace ι →L[ℂ] BrightSpace ι :=
  (brightCoefficient (realMode D hh)).comp (M.comp (bright (realMode D hh)))

theorem brightMatrix_add {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (A B : DefectSpace ι →L[ℂ] DefectSpace ι) :
    brightMatrix D hh (A+B) = brightMatrix D hh A+brightMatrix D hh B := by
  simp only [brightMatrix, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

theorem brightMatrix_sub {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (A B : DefectSpace ι →L[ℂ] DefectSpace ι) :
    brightMatrix D hh (A-B) = brightMatrix D hh A-brightMatrix D hh B := by
  simp only [brightMatrix, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

theorem brightMatrix_norm {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (A : DefectSpace ι →L[ℂ] DefectSpace ι) : ‖brightMatrix D hh A‖ ≤ ‖A‖ := by
  exact contractive_compression_norm _ _ _
    (brightCoefficient_norm_le (ι := ι) (realMode D hh) (realMode_norm D hh))
    (bright_norm_le (ι := ι) (realMode D hh) (realMode_norm D hh))

omit [Fintype ι] in
theorem brightMatrix_baseline {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    brightMatrix (ι := ι) D hh (baseline D hh) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [brightMatrix, ContinuousLinearMap.comp_apply, baseline_bright, map_zero, zero_apply]

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

theorem source_raw_bright_error {L d : ℕ} {z σ Rdiag Rcal : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (v : SourceDecoration.Vertex S precision → ℝ) (α : ℝ) (β : Fin 3 → ℝ)
    (diag : SourceIncidence.V S precision → ℝ)
    (hdiag : 0 ≤ Rdiag) (hcal : 0 ≤ Rcal)
    (hv : ∀ i, |(v i)⁻¹-(muH D (inverse_length_le_1024 hL)+
      (SourceIncidence.graph S precision).targetMatrix α
        (fun e => β (SourceIncidence.axis S precision e)) diag i i)| ≤ Rdiag)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ Rcal) :
    ‖brightMatrix D (inverse_length_le_1024 hL)
      (auxiliaryMatrix D hσ0 hσ (centers L d (SourceDecoration.site S precision)) v)-
      logicalTarget (SourceIncidence.graph S precision) α
        (fun e => β (SourceIncidence.axis S precision e)) diag‖ ≤
      Rdiag+3*Rcal+Cs*(L : ℝ)^5*(256*(((3 : ℝ)^d)⁻¹)^2+
        (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Real.exp (-cs*(L : ℝ)))+
        16*σ*(L : ℝ)^4 := by
  let p := SourceDecoration.site S precision
  let hh := inverse_length_le_1024 hL
  let G := SourceIncidence.graph S precision
  let b := fun e => β (SourceIncidence.axis S precision e)
  let Θ := G.targetMatrix α b diag
  let N := blockOperator (nearBlocks D d p)
  let F := blockOperator (shellBlocks D le_rfl (by positivity) d p 2)
  let E := compressed (L : ℝ)⁻¹ (centers L d p) (resolvent D hσ0 hσ)-
    compressed (L : ℝ)⁻¹ (centers L d p) (resolvent D le_rfl (by positivity))
  have htarget : ComplexInverse.complexOperator Θ =
      ComplexInverse.complexOperator (Matrix.diagonal fun i => Θ i i)+
        ComplexInverse.complexOperator (PhysicalBright.incidenceMatrix G b) := by
    have ht := congrArg (fun A => ComplexInverse.complexOperator A)
      (PhysicalBright.targetMatrix_split G α b diag)
    simpa only [complexOperator_add] using ht
  have he : brightMatrix D hh (auxiliaryMatrix D hσ0 hσ (centers L d p) v)-
      ComplexInverse.complexOperator Θ =
      (brightMatrix D hh (onsiteShift D hh v)-
        ComplexInverse.complexOperator (Matrix.diagonal fun i => Θ i i))+
      (-brightMatrix D hh N-ComplexInverse.complexOperator (PhysicalBright.incidenceMatrix G b))-
      brightMatrix D hh F-brightMatrix D hh E := by
    rw [auxiliaryMatrix_decomposition D hh hσ0 hσ d p (SourceDecoration.site_injective S precision) v,
      brightMatrix_sub, brightMatrix_sub, brightMatrix_add, brightMatrix_baseline, zero_add,
      offsite_near_far, brightMatrix_add, htarget]
    dsimp only [N, F, E]
    abel
  have hround : ‖brightMatrix D hh (onsiteShift D hh v)-
      ComplexInverse.complexOperator (Matrix.diagonal fun i => Θ i i)‖ ≤ Rdiag :=
    onsite_bright_error D hh v (fun i => Θ i i) hdiag hv
  have hnear : ‖-brightMatrix D hh N-
      ComplexInverse.complexOperator (PhysicalBright.incidenceMatrix G b)‖ ≤ 3*Rcal :=
    source_near_calibration_norm S precision hL D d β hcal hβ
  have hfar : ‖brightMatrix D hh F‖ ≤ Cs*(L : ℝ)^5*(256*(((3 : ℝ)^d)⁻¹)^2+
      (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Real.exp (-cs*(L : ℝ))) :=
    (brightMatrix_norm D hh F).trans
      (nonneighbor_operator_norm hL D le_rfl (by positivity) hd p (SourceDecoration.site_injective S precision))
  have hdisj : Pairwise fun i j => Disjoint
      (Metric.ball (centers L d p i) ((L : ℝ)⁻¹)⁻¹)
      (Metric.ball (centers L d p j) ((L : ℝ)⁻¹)⁻¹) := by
    simpa only [inv_inv] using centers_disjoint (inv_pos.mp D.h_pos) hd p (SourceDecoration.site_injective S precision)
  have hdet : ‖brightMatrix D hh E‖ ≤ 16*σ*(L : ℝ)^4 := by
    have ht := (brightMatrix_norm D hh E).trans (compressed_detuning D hσ0 hσ (centers L d p) hdisj)
    simpa only [inv_pow, inv_inv] using ht
  change ‖brightMatrix D hh (auxiliaryMatrix D hσ0 hσ (centers L d p) v)-
    ComplexInverse.complexOperator Θ‖ ≤ _
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hround hnear)) hfar)) hdet)

#print axioms source_raw_bright_error

end Maxwell.Continuum.FiniteAuxiliary
