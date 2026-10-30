import Maxwell.Continuum.SourceRoutingPathNextFields

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

def footerWork : Finset ℕ := {1253,1255}∪wordWork
def levelIncrement : List NatAssign.Instruction := [.add 1219 1233]
def footerCode : Code := .seq (loadCode 1234 1253) (.seq (NatAssign.code levelIncrement)
  (.seq (loadCode 1233 1255) (NatAssign.code nextCleanup)))

theorem footer_executes {q : ℕ} (p : GeometryHistory.Plan q) (k next level cursor B : ℕ) (v : ℕ→ℕ)
    (fields : NextFields p k next v) (levelValue : v 1233=level)
    (width : ∀j∈ids,(v j).bits.length ≤ B) (cursorWidth : cursor.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (bank : NatAssign.Bank ids v s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (cursorWord : Word s.val 1253 cursor) (levelWord : Word s.val 1255 level) :
    ∃steps t,Executes input tape footerCode steps s t ∧ steps ≤ 2^140*(B+3)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed (p.layer (k+1)) (k+2) next) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Word t.val 1253 (v 1234) ∧ Word t.val 1255 (level+1) ∧
      BinaryPrecision.Frame footerWork s.val t.val := by
  obtain ⟨c0,a,e0,h0,ca,f0⟩:=copyWord_executes 1234 1253 cursor (v 1234) (by decide)
    input tape s (bank 1234 (by decide)) cursorWord
  have ba:=bank_of_frame bank f0 (by decide)
  have za:=ready.of_tapes (fun j hj => f0.tapes j (by simp only [Finset.mem_singleton];omega))
  have a1249:=RationalAccumulator.blank_of_eq (f0.tapes 1249 (by decide)) privateBlank
  have values : NatAssign.values levelIncrement v=Function.update v 1233 (level+1) := by
    simp [levelIncrement,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,fields.one,levelValue,Nat.add_comm]
  obtain ⟨c1,b,e1,h1,bb,zb,f1⟩:=stage levelIncrement
    (by simp [levelIncrement,NatAssign.Instruction.Valid,ids,controls]) v B width
    (by simp [levelIncrement,NatAssign.Instruction.literalWidth]) input tape a ba za
  have bb' : NatAssign.Bank ids (Function.update v 1233 (level+1)) b.val := by rw [←values];exact bb
  have b1249:=RationalAccumulator.blank_of_eq (f1.tapes 1249 (by decide)) a1249
  have width' : ∀j∈ids,((Function.update v 1233 (level+1)) j).bits.length ≤ 2*B+1 := by
    have h:=NatAssign.instruction_width ids (.add 1219 1233)
      (by simp [NatAssign.Instruction.Valid,ids,controls]) v B width (by simp [NatAssign.Instruction.literalWidth])
    simpa only [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      fields.one,levelValue,Nat.add_comm] using h
  obtain ⟨c2,c,e2,h2,lc,f2⟩:=copyWord_executes 1233 1255 level (level+1) (by decide) input tape b
    (by simpa only [Function.update_self] using bb' 1233 (by decide))
    (RationalAccumulator.word_of_eq ((f1.tapes 1255 (by decide)).trans (f0.tapes 1255 (by decide))) levelWord)
  have bc:=bank_of_frame bb' f2 (by decide)
  have zc:=zb.of_tapes (fun j hj => f2.tapes j (by simp only [Finset.mem_singleton];omega))
  have c1249:=RationalAccumulator.blank_of_eq (f2.tapes 1249 (by decide)) b1249
  obtain ⟨c3,t,e3,h3,bt,zt,t1249,f3⟩:=nextCleanup_executes p k next (2*B+1)
    (Function.update v 1233 (level+1)) (fields.level_update _) width' input tape c bc zc c1249
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,bt,zt,t1249,
    RationalAccumulator.word_of_eq ((f3.tapes 1253 (by decide)).trans
      ((f2.tapes 1253 (by decide)).trans (f1.tapes 1253 (by decide)))) ca,
    RationalAccumulator.word_of_eq (f3.tapes 1255 (by decide)) lc,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans ((f2.mono (by decide)).trans (f3.mono (by decide))))⟩
  have levelWidth : level.bits.length ≤ B := by simpa only [levelValue] using width 1233 (by decide)
  have nextWidth:=width 1234 (by decide)
  have incrementWidth : (level+1).bits.length ≤ 2*B+1 := by simpa only [Function.update_self] using width' 1233 (by decide)
  change c1 ≤ 3000*8^1*(B+2)^2 at h1
  nlinarith only [h0,h1,h2,h3,levelWidth,nextWidth,incrementWidth,cursorWidth]

#print axioms footer_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
