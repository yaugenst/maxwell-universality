import Maxwell.Continuum.CalibrationNeighborControl

/-! The two noncentral projections in the actual perturbation are tested
from the literal row and column alias coordinates. -/

namespace Maxwell.Continuum.Calibration.RawFree

open RationalDataflow FreeFiber
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def columnCentralBody : List Instruction :=
  [.binary .add 37 28 20,.binary .mul 37 28 37,.binary .mul 37 37 37,
   .binary .add 38 29 20,.binary .mul 38 29 38,.binary .mul 38 38 38,.binary .add 37 37 38,
   .binary .add 38 30 20,.binary .mul 38 30 38,.binary .mul 38 38 38,.binary .add 37 37 38]

def matrixGuardInstructions : List Instruction :=
  centralInstructions++columnCentralBody++[.binary .mul 39 21 37]
def matrixGuard (v : ℕ → Parts) : ℕ → Parts := RationalDataflow.evaluate matrixGuardInstructions v

theorem matrixGuard_keep (v : ℕ → Parts) (k : ℕ)
    (hk : k≠20 ∧ k≠21 ∧ k≠22 ∧ k≠37 ∧ k≠38 ∧ k≠39) : matrixGuard v k=v k := by
  simp [matrixGuard,matrixGuardInstructions,centralInstructions,columnCentralBody,RationalDataflow.evaluate,
    Instruction.update,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2.1,hk.2.2.2.2.2]

theorem matrixGuard_product (v : ℕ → Parts) : matrixGuard v 39=
    (centralMetric (coordinates v)).mul (centralMetric (columnCoordinates v)) := by
  simp [matrixGuard,matrixGuardInstructions,centralInstructions,columnCentralBody,RationalDataflow.evaluate,
    Instruction.update,BinaryOp.eval,centralMetric,sumThree,coordinates,columnCoordinates]

theorem matrixGuard_valid : ∀ a ∈ matrixGuardInstructions, a.Valid neighborRegisters := by
  simp [matrixGuardInstructions,centralInstructions,columnCentralBody,Instruction.Valid,neighborRegisters]

theorem matrixGuard_admissible (v : ℕ → Parts) : AdmissibleTrace matrixGuardInstructions v := by
  simp [matrixGuardInstructions,centralInstructions,columnCentralBody,AdmissibleTrace,Instruction.Admissible]

theorem matrixGuard_good (v : ℕ → Parts) (hg : Good neighborRegisters v) :
    Good neighborRegisters (matrixGuard v) :=
  evaluate_good neighborRegisters matrixGuardInstructions matrixGuard_valid v hg (matrixGuard_admissible v)

theorem matrixGuard_noncentral (v : ℕ → Parts) (hg : Good neighborRegisters v) (ν μ : Alias)
    (hν : ∀ k, (coordinates v k).value=(ν k : ℚ))
    (hμ : ∀ k, (columnCoordinates v k).value=(μ k : ℚ)) :
    0<(matrixGuard v 39).value ↔ ¬IsCentralAlias ν ∧ ¬IsCentralAlias μ := by
  have hc (k : Fin 3) : (coordinates v k).Valid := by fin_cases k <;> exact hg _ (by decide)
  have hm (k : Fin 3) : (columnCoordinates v k).Valid := by fin_cases k <;> exact hg _ (by decide)
  have hn := centralMetric_nonneg (coordinates v) hc
  have hn' := centralMetric_nonneg (columnCoordinates v) hm
  have hz := centralMetric_pos (coordinates v) hc ν hν
  have hz' := centralMetric_pos (columnCoordinates v) hm μ hμ
  rw [matrixGuard_product,Parts.mul_value]
  constructor
  · intro hp
    rcases mul_pos_iff.mp hp with hp | hn
    · exact ⟨hz.mp hp.1,hz'.mp hp.2⟩
    · linarith [hn.2]
  · rintro ⟨hν,hμ⟩
    exact mul_pos (hz.mpr hν) (hz'.mpr hμ)

#print axioms matrixGuard_noncentral

end Maxwell.Continuum.Calibration.RawFree
