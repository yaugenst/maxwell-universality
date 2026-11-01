import Maxwell.Continuum.CalibrationCentralReset

/-! The inverse output is copied back to a fixed ordinary register interval;
the large internal matrix workspace remains isolated and reusable. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes relocation gap

def outputNative : Finset ℕ := Finset.Ico 2728 4456
def outputRegisters : Finset ℕ := Finset.Ico 1700 2276
def outputPorts : Finset ℕ := Finset.Ico 6100 7828
def outputSources : List ℕ := (outputNative.sort (·≤·)).map relocation
def outputTarget (i : ℕ) : ℕ := relocation i+3372
def outputPlan : List NatAssign.Instruction := NatAssign.copies outputSources outputTarget
def outputCode : Code := NatAssign.code outputPlan
def outputIds : Finset ℕ := outputNative.image relocation∪outputPorts
def outputWords (v old : ℕ→Parts) (i : ℕ) : ℕ :=
  if i<gap then dataValues old i else dataValues v (relocation i)
def outputParts (v : ℕ→Parts) (i : ℕ) : Parts := v (i-1124)
def outputCost (B : ℕ) : ℕ := 3000*8^outputSources.length*(B+2)^2

theorem outputPorts_eq : outputPorts=ports outputRegisters := by
  ext i
  simp only [outputPorts,Finset.mem_Ico,ports,Finset.mem_biUnion,outputRegisters,
    cellPorts,Finset.mem_insert,Finset.mem_singleton,positivePort,negativePort,denominatorPort]
  constructor
  · intro hi
    refine ⟨(i-1000)/3,?_,?_⟩ <;> omega
  · rintro ⟨j,hj,cell⟩
    omega

theorem outputNative_bound (i : ℕ) (hi : i∈outputNative) : 2728≤ i ∧ i<4456 :=
  Finset.mem_Ico.mp hi

theorem outputNative_member (i : ℕ) (hi : i∈outputNative) : i∈ids bank := by
  have bounds:=outputNative_bound i hi
  let j:=(i-1000)/3
  have member : j∈bank := by
    simp only [bank,MatrixInverse.registers,Finset.mem_range]
    have hbase : MatrixInverse.base 24=1152 := by decide
    rw [hbase]
    dsimp only [j]
    omega
  apply cell_mem member
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton,positivePort,negativePort,denominatorPort]
  dsimp only [j]
  omega

theorem outputNative_moved (i : ℕ) (hi : i∈outputNative) : relocation i=i+gap :=
  moved i (by have :=outputNative_bound i hi;omega) (bank_bound i (outputNative_member i hi))

theorem outputSources_member (i : ℕ) : i∈outputSources ↔ i∈outputNative.image relocation := by
  simp only [outputSources,List.mem_map,Finset.mem_sort,Finset.mem_image]

theorem outputTarget_member (i : ℕ) (hi : i∈outputSources) : outputTarget i∈outputPorts := by
  obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp ((outputSources_member i).mp hi)
  rw [outputTarget,relocation_involutive]
  have bounds:=outputNative_bound j hj
  exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩

theorem outputTarget_separate : ∀i∈outputSources,∀j∈outputSources,outputTarget i≠j := by
  intro i hi j hj
  have target:=Finset.mem_Ico.mp (outputTarget_member i hi)
  obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp ((outputSources_member j).mp hj)
  rw [outputNative_moved k hk]
  have lower : 20000≤gap := by unfold gap;have :=count_lower;omega
  omega

theorem outputTarget_injective : ∀i∈outputSources,∀j∈outputSources,outputTarget i=outputTarget j→i=j := by
  intro i _ j _ eq
  exact relocation.injective (Nat.add_right_cancel eq)

theorem outputIds_ge : ∀i∈outputIds,4≤ i := by
  intro i hi
  rcases Finset.mem_union.mp hi with source|target
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp source
    rw [outputNative_moved j hj]
    have :=outputNative_bound j hj
    omega
  · have :=Finset.mem_Ico.mp target
    omega

theorem outputWords_source (v old : ℕ→Parts) (i : ℕ) (hi : i∈outputNative) :
    outputWords v old (relocation i)=dataValues v i := by
  have high : ¬relocation i<gap := by rw [outputNative_moved i hi];omega
  rw [outputWords,ite_eq_right high,relocation_involutive]

theorem outputWords_target (v old : ℕ→Parts) (i : ℕ) (hi : i∈outputPorts) :
    outputWords v old i=dataValues old i := by
  have bounds:=Finset.mem_Ico.mp hi
  have lower : 20000≤gap := by unfold gap;have :=count_lower;omega
  exact ite_eq_left (by omega)

#print axioms outputTarget_separate
end Maxwell.Continuum.Calibration.CentralRelocation
