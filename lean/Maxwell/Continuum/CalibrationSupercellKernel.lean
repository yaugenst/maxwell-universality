import Maxwell.Continuum.CalibrationSupercellAdjoint
import Maxwell.Continuum.CalibrationSupercellOperator

/-! Exact physical matrix blocks of the complete supercell operator.
The inverse grid volume follows from the proved physical isometry. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier PeriodicSampling

variable (M : ℕ) [NeZero M]

def physicalOperator (T : Grid M → FiberSpace →L[ℂ] FiberSpace) : FieldL2 →L[ℂ] FieldL2 :=
  (blockEmbedding M).toContinuousLinearMap.comp
    ((blockOperator M T).comp (blockEmbedding M).toContinuousLinearMap.adjoint)

theorem physicalOperator_apply (T : Grid M → FiberSpace →L[ℂ] FiberSpace) (f : FieldL2) :
    physicalOperator M T f=blockEmbedding M (blockOperator M T (blockAnalysis M f)) := by
  change blockEmbedding M (blockOperator M T ((blockEmbedding M).toContinuousLinearMap.adjoint f))=_
  rw [blockEmbedding_adjoint]

theorem physicalFactor_volume : (8 : ℂ)*(physicalFactor M : ℂ)^2=((M : ℂ)^3)⁻¹ := by
  have hM : (M : ℂ)≠0 := by exact_mod_cast NeZero.ne M
  apply (mul_eq_one_iff_eq_inv₀ (pow_ne_zero 3 hM)).mp
  have h := congrArg (fun x : ℝ => (x : ℂ)) (physicalFactor_square M)
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
    Complex.ofReal_ofNat,Complex.ofReal_one] at h
  convert h using 1
  ring

theorem physicalOperator_cell (T : Grid M → FiberSpace →L[ℂ] FiberSpace)
    (a b : Grid M) (f : CellFieldL2) :
    restrictLatticeCell (representative M a)
      (physicalOperator M T (embedLatticeCell (representative M b) f))=
      ((M : ℂ)^3)⁻¹ • ∑ j : Grid M,
        (cellPhase M j (representative M a)*star (cellPhase M j (representative M b))) •
          cellUnitary M j (T j ((cellUnitary M j).symm f)) := by
  rw [physicalOperator_apply,restrict_blockEmbedding]
  simp only [blockOperator_apply,blockAnalysis_embed,map_smul,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  calc
    _ = ((8 : ℂ)*(physicalFactor M : ℂ)^2)*
        (cellPhase M j (representative M a)*star (cellPhase M j (representative M b))) := by ring
    _ = _ := by rw [physicalFactor_volume]

#print axioms physicalOperator_cell

end Maxwell.Continuum.Calibration.Supercell
