import Maxwell.Continuum.ChebyshevWaveDimensionsExecution
import Maxwell.Continuum.ProfileCacheAllocation
import Maxwell.Continuum.FourierTensorModeRows

/-! The wave-cache dimensions and disjoint heap are calculated from the
stored tensor parameters and the actual Fourier-row descriptors. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def ids : Finset ℕ := dimensionIds∪{200,202,203,204,311,725,726,727,728,1100,1110}
def initial (Q N R width bp bn bd i : ℕ) : ℕ :=
  if i=200 then width else if i=202 then bp else if i=203 then bn else if i=204 then bd
  else if i=311 then R else initialDimensions Q N i
def afterDimensions (Q N R width bp bn bd i : ℕ) : ℕ :=
  if i∈dimensionIds then finalDimensions Q N i else initial Q N R width bp bn bd i
def plan : List NatAssign.Instruction :=
  [.copy 311 1100,.literal 728 2,.multiply 728 1100,.literal 728 1,.add 728 1100,
   .copy 1100 727,.multiply 727 1100,.multiply 727 1100,
   .copy 712 1110,.copy 716 725,.literal 728 2,.multiply 728 725,
   .copy 714 726,.literal 728 7,.add 728 726,
   .copy 1100 727,.literal 728 5,.multiply 728 727,.multiply 200 727,
   .add 202 727,.add 203 727,.add 204 727,.literal 728 0]
def values (Q N R width bp bn bd : ℕ) : ℕ→ℕ :=
  NatAssign.values plan (afterDimensions Q N R width bp bn bd)
def heap (R width bp bn bd : ℕ) : ℕ := bp+bn+bd+5*RowArithmetic.rowCount R*width
def slotWidth (Q N : ℕ) : ℕ := waveWorkBits (8*Q) N+7
def buffer (Q N R : ℕ) (a : Table (5*RowArithmetic.rowCount R)) (memory : ℕ→Bool) :
    Table (2*(waveDegree (8*Q) N+1)) :=
  Profile.Runtime.memoryTable (2*(waveDegree (8*Q) N+1)) (slotWidth Q N)
    (heap R (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) (by unfold slotWidth;omega) memory
def setupCode : Code := .seq dimensionCode (NatAssign.code plan)
def cleared : List ℕ := [712,713,714,715,716,717,718,719,725,726,727,728]
def changed : Finset ℕ := dimensionWorkspace∪{725,726,727,728,1100,1110}∪Profile.Runtime.CacheAllocation.changed

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,dimensionIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega
theorem plan_valid : ∀a∈plan,a.Valid ids := by
  simp [plan,NatAssign.Instruction.Valid,ids,dimensionIds]

theorem initial_dimensions (Q N R width bp bn bd i : ℕ) (hi : i∈dimensionIds) :
    initial Q N R width bp bn bd i=initialDimensions Q N i := by
  simp only [dimensionIds,Finset.mem_insert,Finset.mem_singleton] at hi
  unfold initial
  split_ifs <;> omega

theorem values_aliases (Q N R width bp bn bd : ℕ) :
    values Q N R width bp bn bd 1100=RowArithmetic.rowCount R := by
  simp [values,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,afterDimensions,dimensionIds,initial,
    RowArithmetic.rowCount,Calibration.aliasSide]
  ring
theorem values_degree (Q N R width bp bn bd : ℕ) :
    values Q N R width bp bn bd 1110=waveDegree (8*Q) N := by
  simp [values,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,afterDimensions,dimensionIds,finalDimensions_eq,scannedValues,
    degreeValues_eq]
theorem values_length (Q N R width bp bn bd : ℕ) :
    values Q N R width bp bn bd 725=2*(waveDegree (8*Q) N+1) := by
  simp [values,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,afterDimensions,dimensionIds,finalDimensions_count]
theorem values_width (Q N R width bp bn bd : ℕ) :
    values Q N R width bp bn bd 726=slotWidth Q N := by
  simp [values,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,afterDimensions,dimensionIds,finalDimensions_work,slotWidth]
  omega
theorem values_heap (Q N R width bp bn bd : ℕ) :
    values Q N R width bp bn bd 727=heap R width bp bn bd := by
  simp [values,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,afterDimensions,dimensionIds,initial,
    heap,RowArithmetic.rowCount,Calibration.aliasSide]
  ring
theorem values_zero (Q N R width bp bn bd : ℕ) : values Q N R width bp bn bd 728=0 := by
  simp [values,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value]

theorem source_separated (Q N R : ℕ) (a : Table (5*RowArithmetic.rowCount R)) (memory : ℕ→Bool) :
    a.SeparatedFrom (buffer Q N R a memory) := by
  intro x hx y hy
  have hbase : addressValue x≤addressValue a.basePositive+addressValue a.baseNegative+
      addressValue a.baseDenominator := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> omega
  simp only [buffer,Profile.Runtime.memoryTable,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl|rfl|rfl <;>
    simp only [buffer,Profile.Runtime.memoryTable,addressValue_bits,IncidenceEncoding.Separated] <;>
    left <;> unfold heap <;> omega

#print axioms values_aliases
#print axioms source_separated
end Maxwell.Continuum.Profile.WaveMachine.Runtime.TensorSetup
