import Maxwell.Continuum.CalibrationCentralRelocation
import Maxwell.Continuum.RationalDataflowRetainedCells
import Maxwell.Cost.Structured.NatAssign.Copies

/-! Copy the actual Schur cells into the isolated matrix bank. Input and
output locations are fixed program literals, independent of their values. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes

def inputRegisters : Finset ℕ := Finset.Ico 500 1076
def inputPorts : Finset ℕ := ports inputRegisters
def inputSources : List ℕ := inputPorts.sort (·≤·)
def inputTarget (i : ℕ) : ℕ := relocation (i-1500)
def inputPlan : List NatAssign.Instruction := NatAssign.copies inputSources inputTarget
def inputCode : Code := NatAssign.code inputPlan
def matrixParts (v : ℕ→Parts) (i : ℕ) : Parts := if i<576 then v (500+i) else Initialize.parts i
def inputIds : Finset ℕ := inputPorts∪(ids bank).image relocation
def inputWords (v : ℕ→Parts) (i : ℕ) : ℕ :=
  if 2500≤ i ∧ i<4228 then dataValues v i else dataValues Initialize.parts (relocation i)

theorem inputPorts_bounds (i : ℕ) (hi : i∈inputPorts) : 2500≤ i ∧ i<4228 := by
  obtain ⟨j,hj,cell⟩:=Finset.mem_biUnion.mp hi
  have bounds:=Finset.mem_Ico.mp hj
  simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton] at cell
  omega

theorem mem_inputPorts (i : ℕ) (lo : 2500≤ i) (hi : i<4228) : i∈inputPorts := by
  let j:=(i-1000)/3
  have bounds : 500≤ j ∧ j<1076 := by dsimp only [j];omega
  refine Finset.mem_biUnion.mpr ⟨j,Finset.mem_Ico.mpr bounds,?_⟩
  simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton]
  dsimp only [j]
  omega

theorem inputTarget_value (i : ℕ) (hi : i∈inputPorts) : inputTarget i=i-1500+gap := by
  apply moved
  · have :=inputPorts_bounds i hi;omega
  · have :=inputPorts_bounds i hi
    unfold count
    omega

theorem inputTarget_separate : ∀i∈inputSources,∀j∈inputSources,inputTarget i≠j := by
  intro i hi j hj
  have hi':i∈inputPorts:=by simpa only [inputSources,Finset.mem_sort] using hi
  have hj':j∈inputPorts:=by simpa only [inputSources,Finset.mem_sort] using hj
  rw [inputTarget_value i hi']
  have h:=inputPorts_bounds j hj'
  unfold gap count
  omega

theorem inputTarget_injective : ∀i∈inputSources,∀j∈inputSources,inputTarget i=inputTarget j→i=j := by
  intro i hi j hj eq
  have hi':i∈inputPorts:=by simpa only [inputSources,Finset.mem_sort] using hi
  have hj':j∈inputPorts:=by simpa only [inputSources,Finset.mem_sort] using hj
  rw [inputTarget_value i hi',inputTarget_value j hj'] at eq
  have bi:=inputPorts_bounds i hi'
  have bj:=inputPorts_bounds j hj'
  omega

theorem small_in_bank (i : ℕ) (hi : i<576) : i∈bank := by
  simp only [bank,MatrixInverse.registers,Finset.mem_range]
  have hbase : MatrixInverse.base 24=1152 := by decide
  rw [hbase]
  omega

theorem inputTarget_member (i : ℕ) (hi : i∈inputPorts) : inputTarget i∈(ids bank).image relocation := by
  obtain ⟨j,hj,cell⟩:=Finset.mem_biUnion.mp hi
  have bounds:=Finset.mem_Ico.mp hj
  refine Finset.mem_image.mpr ⟨i-1500,?_,rfl⟩
  apply cell_mem (small_in_bank (j-500) (by omega))
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton,positivePort,negativePort,denominatorPort] at cell ⊢
  omega

theorem inputPorts_bank (v : ℕ→Parts) (s : BitRAMState) (cells : Cells inputRegisters v s) :
    NatAssign.Bank inputPorts (dataValues v) s := by
  intro i hi
  obtain ⟨j,hj,cell⟩:=Finset.mem_biUnion.mp hi
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at cell
  rcases cell with rfl|rfl|rfl
  · simpa only [dataValues_positive] using (cells j hj).1
  · rw [dataValues_negative]
    exact (cells j hj).2.1
  · rw [dataValues_denominator]
    exact (cells j hj).2.2

theorem matrixParts_good (v : ℕ→Parts) (good : Good inputRegisters v) : Good bank (matrixParts v) := by
  intro i _
  by_cases hi:i<576
  · exact (show (matrixParts v i).Valid from by
      rw [matrixParts,ite_eq_left hi]
      exact good (500+i) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))
  · simpa only [matrixParts,ite_eq_right hi,Initialize.parts] using Parts.literal_valid 0

theorem matrixParts_width (v : ℕ→Parts) (B : ℕ) (hB : 1≤ B)
    (width : WidthBank inputRegisters B v) : WidthBank bank B (matrixParts v) := by
  intro i _
  by_cases hi:i<576
  · rw [matrixParts,ite_eq_left hi]
    exact width (500+i) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
  · rw [matrixParts,ite_eq_right hi]
    exact (show (Initialize.parts i).Width 1 from by
      norm_num [Initialize.parts,Parts.literal,Parts.Width]).mono hB

#print axioms inputTarget_member
end Maxwell.Continuum.Calibration.CentralRelocation
