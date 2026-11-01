import Maxwell.Continuum.CalibrationFiniteAlgorithm
import Maxwell.Cost.Structured.NatAssign.WordLength
import Maxwell.Codec.NaturalLength

/-! Fixed natural-word arithmetic for the finite calibration dimensions.
Inputs4400..4403 contain L, the placement radius, requested precision, and
the fourth power of the retained master constant. All logarithms are
computed by scanning the actual stored binary words. -/
namespace Maxwell.Continuum.Calibration.ParameterMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
attribute [local irreducible] MasterConstants.exponent MasterConstants.Cs

def ids : Finset ℕ := Finset.Icc 4400 4499
def workspace : Finset ℕ := {0,1,2,3}∪ids

def prepare : List NatAssign.Instruction :=
  [.literal 4470 1,.literal 4471 2,.literal 4472 4,.literal 4473 16,.literal 4474 40,
   .literal 4475 96,.literal 4476 200,.literal 4477 256,.literal 4478 (2^106),
   .literal 4479 (2^20),.literal 4480 6,.literal 4481 8,
   .literal 4404 0,.literal 4407 0,.literal 4410 0,
   .copy 4402 4405,.add 4472 4405,.copy 4405 4406,.add 4476 4406,.multiply 4478 4406]

def sizeInstructions : List NatAssign.Instruction :=
  [.copy 4406 4408,.multiply 4474 4408,.add 4405 4408,.add 4407 4408,.add 4477 4408,
   .copy 4408 4482,.add 4475 4482,.add 4404 4482,.add 4471 4482,
   .copy 4482 4483,.multiply 4482 4483,.multiply 4403 4483,.multiply 4400 4483,
   .copy 4400 4484,.add 4401 4484,.add 4470 4484,.multiply 4473 4484,
   .copy 4483 4409,.add 4484 4409,.multiply 4471 4409]

def finish : List NatAssign.Instruction :=
  [.copy 4410 4411,.add 4470 4411,
   .copy 4404 4482,.multiply 4471 4482,
   .copy 4411 4412,.multiply 4472 4412,.add 4482 4412,.add 4408 4412,.add 4477 4412,
   .copy 4404 4413,.multiply 4473 4413,.add 4412 4413,.add 4471 4413,.add 4479 4413,
   .copy 4412 4414,.add 4482 4414,.add 4480 4414,
   .copy 4409 4415,.multiply 4471 4415,.copy 4413 4416,.add 4471 4416,
   .copy 4400 4417,.copy 4404 4418,.multiply 4472 4418,.add 4481 4418]

def prepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values prepare v
def measured (v : ℕ→ℕ) : ℕ→ℕ := Function.update
  (Function.update (prepared v) 4404 (v 4400).bits.length) 4407
  (FiniteAlgorithm.iterations (v 4402)).bits.length
def sized (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values sizeInstructions (measured v)
def sizeMeasured (v : ℕ→ℕ) : ℕ→ℕ := Function.update (sized v) 4410 (sized v 4409).bits.length
def values (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values finish (sizeMeasured v)

def code : Code := .seq (NatAssign.code prepare)
  (.seq (WordLength.code 4400 4404) (.seq (WordLength.code 4406 4407)
    (.seq (NatAssign.code sizeInstructions) (.seq (WordLength.code 4409 4410) (NatAssign.code finish)))))

theorem valid_prepare : ∀a∈prepare,a.Valid ids := by
  simp [prepare,NatAssign.Instruction.Valid,ids]
theorem valid_size : ∀a∈sizeInstructions,a.Valid ids := by
  simp [sizeInstructions,NatAssign.Instruction.Valid,ids]
theorem valid_finish : ∀a∈finish,a.Valid ids := by
  simp [finish,NatAssign.Instruction.Valid,ids]
theorem ids_lower : ∀i∈ids,4 ≤ i := by
  intro i hi;have := (Finset.mem_Icc.mp hi).1;omega

theorem prepared_fields (v : ℕ→ℕ) :
    prepared v 4400=v 4400 ∧ prepared v 4406=FiniteAlgorithm.iterations (v 4402) ∧
    prepared v 4404=0 ∧ prepared v 4407=0 ∧ prepared v 4410=0 := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,FiniteAlgorithm.iterations,
    FiniteAlgorithm.targetPrecision,powerSteps]
  omega

theorem measured_fields (v : ℕ→ℕ) :
    measured v 4404=lengthBits (v 4400) ∧
    measured v 4407=Nat.clog 2 (FiniteAlgorithm.iterations (v 4402)+1) := by
  simp [measured,lengthBits,Codec.clog_two_succ]

theorem sized_fields (v : ℕ→ℕ) (hC : v 4403=2^(4*MasterConstants.exponent)) :
    sized v 4408=FiniteAlgorithm.workPrecision (v 4402) ∧
    sized v 4409=FiniteAlgorithm.size (v 4400) (v 4401) (v 4402) ∧ sized v 4410=0 := by
  have h : sized v 4408=FiniteAlgorithm.workPrecision (v 4402) ∧
      sized v 4409=2*(v 4403*v 4400*(FiniteAlgorithm.workPrecision (v 4402)+96+
        lengthBits (v 4400)+2)^2+16*(v 4400+v 4401+1)) ∧ sized v 4410=0 := by
    simp [sized,sizeInstructions,measured,prepared,prepare,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      FiniteAlgorithm.workPrecision,FiniteAlgorithm.iterations,FiniteAlgorithm.targetPrecision,
      powerWorkPrecision,powerWorkBits,powerSteps,lengthBits,Codec.clog_two_succ]
    constructor <;> ring
  refine ⟨h.1,?_,h.2.2⟩
  rw [hC] at h
  exact h.2.1

structure Outputs (L r N : ℕ) (v : ℕ→ℕ) : Prop where
  length : v 4400=L
  radius : v 4401=r
  requested : v 4402=N
  lengthBits : v 4404=Calibration.lengthBits L
  iterations : v 4406=FiniteAlgorithm.iterations N
  workPrecision : v 4408=FiniteAlgorithm.workPrecision N
  size : v 4409=FiniteAlgorithm.size L r N
  rootBits : v 4411=FiniteAlgorithm.rootBits L r N
  precision : v 4412=FiniteAlgorithm.precision L r N
  inverseSteps : v 4413=FiniteAlgorithm.inverseSteps L r N
  cutoffBits : v 4414=FiniteAlgorithm.cutoffBits L r N
  scaleNum : v 4415=2*FiniteAlgorithm.size L r N
  aliasRadius : v 4416=FiniteAlgorithm.inverseSteps L r N+2
  scaleDen : v 4417=L
  energyPrecision : v 4418=4*L.bits.length+8

theorem output_values (v : ℕ→ℕ) (hC : v 4403=2^(4*MasterConstants.exponent)) :
    Outputs (v 4400) (v 4401) (v 4402) (values v) := by
  obtain ⟨work,size,zero⟩ := sized_fields v hC
  have retained (i : ℕ) (hi : i=4400 ∨ i=4401 ∨ i=4402 ∨ i=4404 ∨ i=4406 ∨ i=4470 ∨
      i=4471 ∨ i=4472 ∨ i=4473 ∨ i=4477 ∨ i=4479 ∨ i=4480 ∨ i=4481) :
      sized v i=measured v i := by
    unfold sized
    apply NatAssign.values_preserves
    intro a ha
    simp only [sizeInstructions,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [NatAssign.Instruction.target];omega
  constructor <;>
    simp [values,finish,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,sizeMeasured,work,size,retained,measured,prepared,prepare,
      FiniteAlgorithm.rootBits,FiniteAlgorithm.precision,FiniteAlgorithm.inverseSteps,
      FiniteAlgorithm.cutoffBits,FiniteAlgorithm.iterations,FiniteAlgorithm.targetPrecision,
      powerSteps,aliasSteps,cutoffWorkBits,lengthBits,Codec.clog_two_succ] <;> ring

#print axioms output_values
end Maxwell.Continuum.Calibration.ParameterMachine
