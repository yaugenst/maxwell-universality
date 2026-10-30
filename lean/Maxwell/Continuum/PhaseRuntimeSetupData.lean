import Maxwell.Continuum.MachinRuntimeCode
import Maxwell.Continuum.PhaseMachineFinalData
import Maxwell.Continuum.StoredWordLength

/-! The fixed phase setup reads rational operands and precision words,
counts the binary length of the range bound, and computes the exact existing
Machin precision and Taylor order with fixed integer instructions. -/
namespace Maxwell.Continuum.PhaseMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def extras : Finset ℕ := {607,608,619,628,632,633,650,651,652,653,654,655,656,657}
def ids : Finset ℕ := PhaseMachine.allIds∪extras
def workspace : Finset ℕ := {0,1,2,3}∪ids
def initialValues (a b Q N i : ℕ) : ℕ :=
  if i=650 then a else if i=651 then b else if i=652 then Q else if i=653 then N else 0
def scannedValues (a b Q N : ℕ) : ℕ→ℕ :=
  Function.update (initialValues a b Q N) 654 Q.bits.length
def setup : List NatAssign.Instruction :=
  [.copy 653 630,.add 654 630,.literal 656 4,.add 656 630,
   .copy 652 655,.literal 656 1,.add 656 655,.copy 655 657,.multiply 657 655,
   .literal 656 800,.multiply 656 655,.copy 653 657,.literal 656 2,.multiply 656 657,
   .add 657 655,.literal 656 13,.add 656 655,.literal 656 0,.literal 657 0]
def setupValues (a b Q N : ℕ) : ℕ→ℕ := NatAssign.values setup (scannedValues a b Q N)
def setupCode : Code := .seq (WordLength.code 652 654) (NatAssign.code setup)

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · exact PhaseMachine.allIds_ge i hi
  · simp only [extras,Finset.mem_insert,Finset.mem_singleton] at hi
    omega

theorem clog_two_succ (Q : ℕ) : Nat.clog 2 (Q+1)=Q.bits.length := by
  rw [Nat.size_eq_bits_len]
  apply Nat.le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by decide)]
    exact Nat.succ_le_of_lt (Nat.lt_size_self Q)
  · rw [Nat.size_le]
    have h := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (Q+1)
    omega

theorem order_eq (Q N : ℕ) : PhaseMachine.order Q N=800*(Q+1)^2+2*N+13 := by
  unfold PhaseMachine.order Calibration.taylorOrder Calibration.taylorHalfOrder
  rw [show (10*(Q+1))^2=100*(Q+1)^2 by ring]
  omega

theorem setup_valid : ∀a∈setup,a.Valid ids := by
  simp [setup,NatAssign.Instruction.Valid,ids,PhaseMachine.allIds,PhaseMachine.ids,
    RationalTaylor.ids,RationalMagnitude.ids,Machin.allIds,RationalArctan.ids,extras]

theorem setupValues_precision (a b Q N : ℕ) :
    setupValues a b Q N 630=Calibration.phaseBits Q N := by
  simp [setupValues,setup,scannedValues,initialValues,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    Calibration.phaseBits,clog_two_succ]
  omega

theorem setupValues_order (a b Q N : ℕ) : setupValues a b Q N 655=PhaseMachine.order Q N := by
  simp [setupValues,setup,scannedValues,initialValues,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,order_eq]
  ring

theorem setupValues_eq (a b Q N i : ℕ) : setupValues a b Q N i=
    if i=630 then Calibration.phaseBits Q N else
    if i=655 then PhaseMachine.order Q N else scannedValues a b Q N i := by
  by_cases h630 : i=630
  · subst i
    simpa using setupValues_precision a b Q N
  by_cases h655 : i=655
  · subst i
    simpa using setupValues_order a b Q N
  by_cases h656 : i=656
  · subst i
    simp [setupValues,setup,scannedValues,initialValues,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]
  by_cases h657 : i=657
  · subst i
    simp [setupValues,setup,scannedValues,initialValues,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]
  simp [setupValues,setup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,h630,h655,h656,h657]

#print axioms setupValues_eq
end Maxwell.Continuum.PhaseMachine.Runtime
