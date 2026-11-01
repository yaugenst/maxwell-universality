import Maxwell.Continuum.ParameterSourceBudgetData
import Maxwell.Cost.RoutingPorts.Primitives
import Maxwell.Codec.NaturalLength

/-! The source logarithm is measured by scanning the actual binary word
for m+1, using clog₂(m+2)=bitlength(m+1). -/
namespace Maxwell.Continuum.Parameters.SourceLogMachine
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def ids : Finset ℕ := SourceBudgetMachine.ids∪{2200}
def prepare : List NatAssign.Instruction :=
  [.literal 2340 1,.copy 2301 2339,.add 2340 2339,.literal 2200 0]
def finish : List NatAssign.Instruction := [.add 2340 2200]
def code : Code := .seq (NatAssign.code prepare)
  (.seq (WordLength.code 2339 2200) (NatAssign.code finish))
def workspace : Finset ℕ := {0,1,2,3,2200,2339,2340}
def preparedWidth (B : ℕ) : ℕ := 16*(B+2)
def cost (B : ℕ) : ℕ := 3000*8^4*(B+3)^2+
  (48*(preparedWidth B+1)^2+1+3000*8*(preparedWidth B+2)^2)

theorem valid_prepare : ∀a∈prepare,a.Valid ids := by
  simp [prepare,NatAssign.Instruction.Valid,ids,SourceBudgetMachine.ids,
    SourceBudgetMachine.extra,SourceBudgetMachine.outputs]
theorem valid_finish : ∀a∈finish,a.Valid ids := by
  simp [finish,NatAssign.Instruction.Valid,ids,SourceBudgetMachine.ids,
    SourceBudgetMachine.extra,SourceBudgetMachine.outputs]
theorem ids_lower : ∀i∈ids,4≤ i := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi|hi
  · simp only [SourceBudgetMachine.ids,SourceBudgetMachine.extra,SourceBudgetMachine.outputs,
      Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  · simp only [Finset.mem_singleton] at hi;omega

theorem executes (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost B ∧
      Word t.val 2200 (inputLog (v 2301)) ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  let vp:=NatAssign.values prepare v
  have fields : vp 2340=1 ∧ vp 2339=v 2301+1 ∧ vp 2200=0 := by
    simp [vp,prepare,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,Nat.add_comm]
  have hpw : ∀i∈ids,(vp i).bits.length≤preparedWidth B := by
    have h:=NatAssign.values_width ids prepare valid_prepare v (B+1)
      (fun i hi=>(hw i hi).trans (by omega)) (by simp [prepare,NatAssign.Instruction.literalWidth])
    intro i hi
    exact (Nat.le_add_right _ 1).trans (by simpa [vp,prepare,preparedWidth,Nat.add_assoc] using h i hi)
  obtain ⟨c0,a,e0,h0,ba,sa,f0⟩:=NatAssign.executes ids ids_lower prepare valid_prepare v input tape s bank scratch
  change NatAssign.Bank ids vp a.val at ba
  have c0bound : c0≤3000*8^4*(B+3)^2 := by
    have hp:=NatAssign.price_bound ids prepare valid_prepare v (B+1)
      (fun i hi=>(hw i hi).trans (by omega)) (by simp [prepare,NatAssign.Instruction.literalWidth])
    exact h0.trans (by simpa [prepare,Nat.add_assoc] using hp)
  have a2339 : Word a.val 2339 (v 2301+1) := by simpa only [fields.2.1] using ba 2339 (by decide)
  have a2200 : Blank a.val 2200 := by
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa only [fields.2.2] using ba 2200 (by decide)
  obtain ⟨c1,b,e1,h1,word,f1⟩:=RoutingPorts.wordLength 2339 2200 (by decide) input tape (v 2301+1) a a2339 a2200
  let vb:=Function.update vp 2200 (v 2301+1).bits.length
  have bb : NatAssign.Bank ids vb b.val := by
    intro i hi
    by_cases he : i=2200
    · subst i;simpa [vb] using word
    · simpa only [vb,Function.update_of_ne he] using
        RationalAccumulator.word_of_eq (f1.tapes i (by simpa using he)) (ba i hi)
  have sb : NatAssign.Scratch b.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (f1.tapes i (by simp;omega)) (sa i hi)
  have baseWidth : (v 2301+1).bits.length≤preparedWidth B := by
    simpa only [fields.2.1] using hpw 2339 (by decide)
  have wb : ∀i∈ids,(vb i).bits.length≤preparedWidth B := by
    intro i hi
    by_cases he : i=2200
    · subst i
      have sizeBound : ((v 2301+1).bits.length).bits.length≤(v 2301+1).bits.length := by
        simpa only [WordLength.countBits_eq] using WordLength.countBits_length (v 2301+1).bits.length
      simpa only [vb,Function.update_self] using
        sizeBound.trans baseWidth
    · simpa only [vb,Function.update_of_ne he] using hpw i hi
  obtain ⟨c2,t,e2,h2,bt,st,f2⟩:=NatAssign.executes ids ids_lower finish valid_finish vb input tape b bb sb
  have c2bound : c2≤3000*8*(preparedWidth B+2)^2 := by
    have hp:=NatAssign.price_bound ids finish valid_finish vb (preparedWidth B) wb
      (by simp [finish,NatAssign.Instruction.literalWidth])
    exact h2.trans (by simpa [finish] using hp)
  have c1bound : c1≤48*(preparedWidth B+1)^2+1 := by
    exact h1.trans (by gcongr)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),Nat.add_le_add c0bound (Nat.add_le_add c1bound c2bound),?_,st,
    (f0.mono (by decide +kernel)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))⟩
  have hh:=bt 2200 (by decide)
  have value : NatAssign.values finish vb 2200=inputLog (v 2301) := by
    simp only [finish,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,Function.update_self,vb,Function.update_of_ne (by decide : 2340≠2200),fields.1]
    rw [inputLog,show v 2301+2=(v 2301+1)+1 by omega,Codec.clog_two_succ]
  simpa only [value] using hh

#print axioms executes
end Maxwell.Continuum.Parameters.SourceLogMachine
