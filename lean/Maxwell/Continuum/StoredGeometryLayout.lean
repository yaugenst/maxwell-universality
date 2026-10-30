import Maxwell.Continuum.SourceGeometryPacking
import Maxwell.Continuum.RationalDataflowArrayRead
import Maxwell.Continuum.NaturalBankStage

/-! Concrete tape and memory boundary for the chronological placement
serializer. Routing supplies one packed natural array; all subsequent
coordinate arithmetic uses the disjoint 960--989 bank. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical.Routing
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def ids : Finset ℕ := (((Finset.Icc 960 989).erase 962).erase 972).erase 973

theorem ids_ge (i : ℕ) (hi : i∈ids) : 960 ≤ i := by
  simp only [ids,Finset.mem_erase,Finset.mem_Icc] at hi
  omega

structure Descriptor (vertices edges words base width : ℕ) (clock : List Bool) (s : BitRAMState) : Prop where
  baseWord : Word s 960 base
  widthWord : Word s 961 width
  clockWord : BankArray.Word s 962 clock
  clockLength : clock.length=width
  verticesWord : Word s 963 vertices
  edgesWord : Word s 964 edges
  wordsWord : Word s 965 words

structure Ready (v : ℕ→ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank ids v s.val
  scratch : BankArray.Scratch s.val
  seven : Blank s.val 7

theorem Ready.natural {v : ℕ→ℕ} {s : Store} (h : Ready v s) : NatAssign.Scratch s.val := by
  intro i hi
  interval_cases i
  · exact h.scratch.1
  · exact h.scratch.2.1
  · exact h.scratch.2.2.1
  · exact h.scratch.2.2.2.1

theorem Ready.stage {v w : ℕ→ℕ} {s t : Store} (h : Ready v s)
    (hb : NatAssign.Bank ids w t.val) (hz : NatAssign.Scratch t.val)
    (hf : BinaryPrecision.Frame ({0,1,2,3}∪ids) s.val t.val) : Ready w t := by
  have keep (i : ℕ) (hi : 4 ≤ i) (hsmall : i<960) : t.val.tapes i=s.val.tapes i := by
    apply hf.tapes
    intro hh
    rcases Finset.mem_union.mp hh with hh | hh
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      omega
    · have := ids_ge i hh
      omega
  exact ⟨hb,⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
    blank_of_eq (keep 5 (by decide) (by decide)) h.scratch.2.2.2.2.1,
    blank_of_eq (keep 6 (by decide) (by decide)) h.scratch.2.2.2.2.2.1,
    blank_of_eq (keep 8 (by decide) (by decide)) h.scratch.2.2.2.2.2.2.1,
    blank_of_eq (keep 9 (by decide) (by decide)) h.scratch.2.2.2.2.2.2.2⟩,
    blank_of_eq (keep 7 (by decide) (by decide)) h.seven⟩

def preparePlan : List NatAssign.Instruction :=
  [.copy 966 982,.multiply 968 982,.add 966 982,.literal 986 8,.add 986 982,
    .copy 966 986,.multiply 967 986,.literal 987 2,.multiply 987 986,
    .multiply 986 983,.multiply 986 984,.multiply 986 985,.literal 969 3,.literal 970 1]

def prepareCode : Code := NatAssign.code preparePlan
def prepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values preparePlan v

theorem preparePlan_valid : ∀a∈preparePlan,a.Valid ids := by
  simp [preparePlan,NatAssign.Instruction.Valid,ids]

theorem prepared_shift (v : ℕ→ℕ) : prepared v 982=v 966+v 966*v 968+8 := by
  simp [prepared,preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value]
  ring

theorem prepared_scale (v : ℕ→ℕ) (j : Fin 3) :
    prepared v (983+j.val)=2*v 966*v 967*v (983+j.val) := by
  fin_cases j <;>
    simp [prepared,preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,Nat.mul_assoc,Nat.mul_comm]

theorem prepare_executes (v : ℕ→ℕ) (W : ℕ) (hW : 4≤W)
    (hv : ∀i∈ids,(v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready v s) :
    ∃cost t,Executes input tape prepareCode cost s t ∧
      cost≤RationalDataflow.stageCost W ∧ Ready (prepared v) t ∧
      BinaryPrecision.Frame ({0,1,2,3}∪ids) s.val t.val := by
  have hfit : ∀a∈preparePlan,a.literalWidth≤4 := by
    simp [preparePlan,NatAssign.Instruction.literalWidth]
    decide
  obtain ⟨cost,t,ex,hc,hb,hz,hf⟩ := RationalDataflow.fixedBankStage_executes ids
    (fun i hi => (by omega : 4≤960).trans (ids_ge i hi)) preparePlan preparePlan_valid
    (by decide) v W hv (fun a ha => (hfit a ha).trans hW)
    input tape s hs.bank hs.natural
  exact ⟨cost,t,ex,hc,hs.stage hb hz hf,hf⟩

#print axioms prepare_executes
end Maxwell.Continuum.GeometryOutput
