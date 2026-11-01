import Maxwell.Cost.PhysicalEmit.Coordinates
import Maxwell.Cost.Structured.NatAssign.Values

/-! Compute the ambient box dimensions and initialize the shared x/y/z
iterator from retained outer-parameter words. -/
namespace Maxwell.Continuum.StoredAmbient
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

def inputs : Finset ℕ := {2221,2240,2241,2242,2244}
def outputs : Finset ℕ := {240,241,242,250,251,252,253,254,255,256,257,258}
def ids : Finset ℕ := inputs∪outputs
def plan : List NatAssign.Instruction :=
  [.literal 256 4,.copy 2221 257,.multiply 2244 257,.add 2221 257,.add 256 257,.literal 256 2,
   .copy 2240 250,.add 257 250,.multiply 256 250,
   .copy 2241 251,.add 257 251,.multiply 256 251,
   .copy 2242 252,.add 257 252,.multiply 256 252,
   .copy 250 258,.multiply 251 258,.multiply 252 258,
   .literal 240 0,.literal 241 0,.literal 242 0,.literal 253 0,.literal 254 0,.literal 255 0]
def prepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values plan v
def side (v : ℕ→ℕ) (j : Fin 3) : ℕ := 2*(v (2240+j.val)+v 2221+v 2221*v 2244+4)
def prepareCode : Code := NatAssign.code plan
def prepareCost (B : ℕ) : ℕ := 3000*8^24*(B+2)^2
def prepareWidth (B : ℕ) : ℕ := 2^24*(B+1)

theorem ids_lower : ∀i∈ids,4≤ i := by
  simp only [ids,inputs,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem valid : ∀a∈plan,a.Valid ids := by
  simp [plan,NatAssign.Instruction.Valid,ids,inputs,outputs]

theorem literals : ∀a∈plan,a.literalWidth≤3 := by
  simp [plan,NatAssign.Instruction.literalWidth]
  decide +kernel

theorem prepared_sides (v : ℕ→ℕ) (j : Fin 3) : prepared v (250+j.val)=side v j := by
  fin_cases j <;>
    simp [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,side] <;> ring

theorem prepared_volume (v : ℕ→ℕ) : prepared v 258=side v 0*side v 1*side v 2 := by
  simp [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,side]
  ring

theorem prepared_loop (v : ℕ→ℕ) (i : ℕ) (hi : i∈PhysicalEmit.loopTapes) : prepared v i=0 := by
  simp only [PhysicalEmit.loopTapes,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [prepared,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value]

theorem prepare_changes : NatAssign.changes plan⊆{0,1,2,3}∪outputs := by
  decide +kernel

theorem prepare_executes (v : ℕ→ℕ) (B : ℕ) (hB : 3≤B)
    (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape prepareCode steps s t ∧ steps≤prepareCost B ∧
      NatAssign.Bank ids (prepared v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(prepared v i).bits.length≤prepareWidth B) ∧
      PhysicalEmit.LowerReady 0 (side v) (prepareWidth B) t.val ∧
      BinaryPrecision.Frame ({0,1,2,3}∪outputs) s.val t.val := by
  obtain ⟨c,t,e,charge,stored,blank,frame⟩:=NatAssign.executes ids ids_lower plan valid v input tape s bank scratch
  change NatAssign.Bank ids (prepared v) t.val at stored
  have bound:=NatAssign.price_bound ids plan valid v B width (fun a ha=>(literals a ha).trans hB)
  have words:=NatAssign.values_width ids plan valid v B width (fun a ha=>(literals a ha).trans hB)
  refine ⟨c,t,e,charge.trans bound,stored,blank,(fun i hi=>Nat.le_of_succ_le (words i hi)),?_,frame.mono prepare_changes⟩
  refine ⟨?_,?_,?_⟩
  · intro j
    have w:=stored (250+j.val) (by fin_cases j <;> decide)
    rw [←prepared_sides v j]
    exact w
  · intro j _
    refine ⟨0,Nat.zero_le _,?_⟩
    have member : PhysicalEmit.coordinateTape j∈PhysicalEmit.loopTapes := by fin_cases j <;> decide
    have w:=stored (PhysicalEmit.coordinateTape j) (by fin_cases j <;> decide)
    rwa [prepared_loop v _ member] at w
  · intro j _
    refine ⟨[],Nat.zero_le _,?_⟩
    have member : PhysicalEmit.counterTape j∈PhysicalEmit.loopTapes := by fin_cases j <;> decide
    have w:=stored (PhysicalEmit.counterTape j) (by fin_cases j <;> decide)
    rwa [prepared_loop v _ member] at w

#print axioms prepare_executes
end Maxwell.Continuum.StoredAmbient
