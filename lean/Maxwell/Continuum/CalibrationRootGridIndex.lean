import Maxwell.Continuum.CalibrationMatrixFlatIndex
import Maxwell.Continuum.CalibrationCenteredGrid

/-! Fixed natural-word decoding for the three-dimensional root quadrature.
The last division reduces the complete Fourier dot product modulo the grid. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.ArrayDecodeMachine (divModValues divModValues_width nat_values_width)
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def ids : Finset ℕ := NaturalQuotient.workPorts∪Finset.Icc 330 341
def first (v : ℕ→ℕ) := divModValues v 330 331 332 333
def second (v : ℕ→ℕ) := divModValues (first v) 332 331 332 334
def third (v : ℕ→ℕ) := divModValues (second v) 332 331 340 335
def dot : List NatAssign.Instruction :=
  [.copy 333 339,.multiply 336 339,.copy 334 340,.multiply 337 340,
   .add 340 339,.copy 335 340,.multiply 338 340,.add 340 339]
def dotted (v : ℕ→ℕ) := NatAssign.values dot (third v)
def values (v : ℕ→ℕ) := divModValues (dotted v) 339 331 340 341
def code : Code := .seq (NaturalDivMod.code 330 331 332 333)
  (.seq (NaturalDivMod.code 332 331 332 334)
    (.seq (NaturalDivMod.code 332 331 340 335)
      (.seq (NatAssign.code dot) (NaturalDivMod.code 339 331 340 341))))

def digits (grid index : ℕ) : Fin 3→ℕ :=
  ![index%grid,(index/grid)%grid,(index/grid/grid)%grid]

theorem digits_lt {grid : ℕ} (hg : 0<grid) (index : ℕ) (i : Fin 3) :
    digits grid index i<grid := by
  fin_cases i <;> exact Nat.mod_lt _ hg

theorem values_coordinates (v : ℕ→ℕ) (i : Fin 3) :
    ![values v 333,values v 334,values v 335] i=digits (v 331) (v 330) i := by
  fin_cases i <;> simp [values,dotted,dot,third,second,first,divModValues,digits,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target]

theorem values_phase (v : ℕ→ℕ) :
    values v 341=(∑i:Fin 3,(![v 336,v 337,v 338] i)*digits (v 331) (v 330) i)%(v 331) := by
  simp [values,dotted,dot,third,second,first,divModValues,digits,Fin.sum_univ_three,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target]
  congr 1
  ring

theorem values_keep (v : ℕ→ℕ) (i : ℕ) (hi : i∉({332,333,334,335,339,340,341}:Finset ℕ)) :
    values v i=v i := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  simp [values,dotted,dot,third,second,first,divModValues,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2]

theorem ids_ge (i : ℕ) (hi : i∈ids) : 10 ≤ i := by
  simp only [ids,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem dot_valid : ∀a∈dot,a.Valid ids := by
  simp [dot,NatAssign.Instruction.Valid,ids,NaturalQuotient.workPorts]

theorem thirds_width (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length≤B) :
    ∀i∈ids,(third v i).bits.length≤B := by
  exact divModValues_width _ ids 332 331 340 335 B (by decide)
    (divModValues_width _ ids 332 331 332 334 B (by decide)
      (divModValues_width v ids 330 331 332 333 B (by decide) hw))

theorem dotted_width (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length≤B) :
    ∀i∈ids,(dotted v i).bits.length≤2^8*(B+1) := by
  simpa only [dotted,show dot.length=8 by rfl] using
    nat_values_width ids dot dot_valid (third v) B (thirds_width v B hw)
      (by simp [dot,NatAssign.Instruction.literalWidth])

theorem values_width (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length≤B) :
    ∀i∈ids,(values v i).bits.length≤2^8*(B+1) :=
  divModValues_width _ ids 339 331 340 341 _ (by decide) (dotted_width v B hw)

theorem thirds_keep (v : ℕ→ℕ) (i : ℕ) (hi : i∈NaturalQuotient.workPorts ∨ i=331) :
    third v i=v i := by
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  simp (disch := omega) [third,second,first,divModValues]

theorem dotted_keep (v : ℕ→ℕ) (i : ℕ) (hi : i∈NaturalQuotient.workPorts ∨ i=331) :
    dotted v i=v i := by
  rw [dotted,values_unchanged dot _ i (by
    have hh := hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
    simp [dot,NatAssign.Instruction.target]
    omega),thirds_keep v i hi]

#print axioms values_phase
#print axioms values_width
end Maxwell.Continuum.RationalDataflow.RootGrid
