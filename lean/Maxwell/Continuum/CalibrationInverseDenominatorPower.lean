import Maxwell.Continuum.ParameterPowerMachine
import Maxwell.Continuum.NatAssignOutputWidth
import Maxwell.Continuum.CalibrationNeumannStep

/-! The common denominator of the integer inverse output is raised to the
actual iteration count by a fixed runtime program. The exponent is read
from the preserved descriptor word; neither the power nor its bits are
supplied as a new numerical input. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.DenominatorPower

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def ids : Finset ℕ := {126,304,530,531,532,533,534}
def changed : Finset ℕ := {0,1,2,3,530,531,532,533,534}
def plan : List NatAssign.Instruction :=
  [.copy 126 530,.literal 531 1,.copy 304 534,.add 531 534]
def code : Code := .seq (NatAssign.code plan) Parameters.PowerMachine.code
def preparedWidth (B : ℕ) : ℕ := 16*(B+1)
def costBound (N B : ℕ) : ℕ :=
  3000*8^4*(B+2)^2+Parameters.PowerMachine.costBound (N+1) (preparedWidth B)

theorem valid : ∀ a∈plan, a.Valid ids := by
  simp [plan,NatAssign.Instruction.Valid,ids]

theorem plan_values (v : ℕ → ℕ) :
    NatAssign.values plan v 530=v 126 ∧ NatAssign.values plan v 531=1 ∧
      NatAssign.values plan v 534=v 304+1 := by
  simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,Nat.add_comm]

theorem executes (v : ℕ → ℕ) (B : ℕ) (hB : 1≤B)
    (hw : ∀ i∈ids, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤costBound (v 304) B ∧
      Word t.val 532 ((v 126)^(v 304+1)) ∧ Word t.val 533 1 ∧
      Word t.val 530 (v 126) ∧ Word t.val 531 1 ∧
      Blank t.val 534 ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame changed s.val t.val := by
  have hid : ∀ i∈ids, 4 ≤ i := by
    intro i hi
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have hl : ∀ a∈plan, a.literalWidth≤B := by
    simp [plan,NatAssign.Instruction.literalWidth,hB]
  obtain ⟨c0,u,e0,hc0,bank0,zero0,f0⟩ :=
    NatAssign.executes ids hid plan valid v input tape s hs hz
  have price := NatAssign.price_bound ids plan valid v B hw hl
  have widths : ∀ i∈ids, (NatAssign.values plan v i).bits.length≤preparedWidth B := by
    intro i hi
    have hh := NatAssign.values_width_bound ids plan valid v B hw hl i hi
    change (NatAssign.values plan v i).bits.length+1≤16*(B+1) at hh
    unfold preparedWidth
    omega
  have bank : NatAssign.Bank SelectedParameters.DynamicPower.ids (NatAssign.values plan v) u.val := by
    intro i hi
    exact bank0 i ((by decide : SelectedParameters.DynamicPower.ids⊆ids) hi)
  have smallWidths : ∀ i∈SelectedParameters.DynamicPower.ids,
      (NatAssign.values plan v i).bits.length≤preparedWidth B := by
    intro i hi
    exact widths i ((by decide : SelectedParameters.DynamicPower.ids⊆ids) hi)
  have count : Word u.val 534 (v 304+1) := by
    simpa only [(plan_values v).2.2] using bank0 534 (by decide)
  have countWidth : (v 304+1).bits.length≤preparedWidth B := by
    simpa only [(plan_values v).2.2] using widths 534 (by decide)
  obtain ⟨c1,t,e1,hc1,ready,blank,frame⟩ := Parameters.PowerMachine.executes
    (NatAssign.values plan v) (v 304+1) (preparedWidth B) (by unfold preparedWidth; omega)
      smallWidths countWidth input tape u bank zero0 count
  have power : Word t.val 532 ((v 126)^(v 304+1)) := by
    simpa [SelectedParameters.DynamicPower.values,(plan_values v).1,
      (plan_values v).2.1] using ready.bank 532 (by decide)
  have one : Word t.val 533 1 := by
    simpa [SelectedParameters.DynamicPower.values,(plan_values v).1,
      (plan_values v).2.1] using ready.bank 533 (by decide)
  have base : Word t.val 530 (v 126) := by
    simpa [SelectedParameters.DynamicPower.values,(plan_values v).1] using ready.bank 530 (by decide)
  have unit : Word t.val 531 1 := by
    simpa [SelectedParameters.DynamicPower.values,(plan_values v).2.1] using ready.bank 531 (by decide)
  refine ⟨c0+c1,t,e0.seq e1,?_,power,one,base,unit,blank,ready.scratch,
    (f0.mono (by decide)).trans (frame.mono (by decide))⟩
  have hcost0 : c0≤3000*8^4*(B+2)^2 := by
    simpa only [plan,List.length_cons,List.length_nil] using hc0.trans price
  exact Nat.add_le_add hcost0 hc1

theorem denominator_width (D N B : ℕ) (hD : D.bits.length≤B) :
    (D^(N+1)).bits.length≤(N+1)*B+1 := by
  exact (SelectedParameters.Geometric.power_bits D (N+1)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hD) _)

theorem costBound_polynomial (N B : ℕ) :
    costBound N B≤2^36*(N+2)^3*(B+2)^2 := by
  unfold costBound Parameters.PowerMachine.costBound Parameters.PowerMachine.bodyCost
    SelectedParameters.DynamicPower.width preparedWidth
  ring_nf
  omega

theorem stored_preserved {n : ℕ} (a : Snapshot n) {s t : BitRAMState}
    (hs : CalibrationMatrix.Horner.Stored a.data a.words s)
    (hf : BinaryPrecision.Frame changed s t) :
    CalibrationMatrix.Horner.Stored a.data a.words t := by
  apply hs.of_memory_tapes hf.memory
  intro i hi
  apply hf.tapes
  simp only [CalibrationMatrix.Horner.Metadata] at hi
  simp only [changed,Finset.mem_insert,Finset.mem_singleton]
  omega

#print axioms executes
#print axioms denominator_width
#print axioms costBound_polynomial
#print axioms stored_preserved

end Maxwell.Continuum.Calibration.NeumannMachine.DenominatorPower
