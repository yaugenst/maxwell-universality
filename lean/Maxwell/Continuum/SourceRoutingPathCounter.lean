import Maxwell.Continuum.SourceRoutingCopyWord

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathCounter
open Structured GeometryArithmetic
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def prepare : List NatAssign.Instruction := [.copy 1200 1230,.multiply 1220 1230]
def cleanup : List NatAssign.Instruction := [.literal 1230 0]
def code : Code := .seq (NatAssign.code prepare) (.seq (loadCode 1230 1242) (NatAssign.code cleanup))
def work : Finset ℕ := {1242}∪GeometryArithmetic.work

theorem executes (v : ℕ→ℕ) (q B : ℕ) (count : v 1200=q) (two : v 1220=2) (zero : v 1230=0)
    (width : ∀j∈ids,(v j).bits.length ≤ B) (countWidth : (2*q).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (bank : NatAssign.Bank ids v s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (counterBlank : Blank s.val 1242) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^32*(B+3)^2 ∧
      NatAssign.Bank ids v t.val ∧ GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Word t.val 1242 (2*q) ∧
      BinaryPrecision.Frame work s.val t.val := by
  have prepared : NatAssign.values prepare v=Function.update v 1230 (2*q) := by
    simp [prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,count,two]
  have cleaned : NatAssign.values cleanup (Function.update v 1230 (2*q))=v := by
    simp only [cleanup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
      Function.update_idem]
    exact Function.update_eq_self_iff.mpr zero.symm
  have width' : ∀j∈ids,((Function.update v 1230 (2*q)) j).bits.length ≤ B := by
    intro j hj
    by_cases same : j=1230
    · simpa only [same,Function.update_self] using countWidth
    · simpa only [Function.update_of_ne same] using width j hj
  obtain ⟨c0,a,e0,h0,ba,za,f0⟩:=stage prepare
    (by simp [prepare,NatAssign.Instruction.Valid,ids,controls]) v B width
    (by simp [prepare,NatAssign.Instruction.literalWidth]) input tape s bank ready
  have ba' : NatAssign.Bank ids (Function.update v 1230 (2*q)) a.val := by rw [←prepared];exact ba
  obtain ⟨c1,b,e1,h1,cb,f1⟩:=copyWord_executes 1230 1242 0 (2*q) (by decide) input tape a
    (by simpa only [Function.update_self] using ba' 1230 (by decide))
    ((RationalAccumulator.zero_word_iff_blank _ _).mpr (RationalAccumulator.blank_of_eq (f0.tapes 1242 (by decide)) counterBlank))
  have bb:=bank_of_frame ba' f1 (by decide)
  have zb:=za.of_tapes (fun j hj => f1.tapes j (by simp only [Finset.mem_singleton];omega))
  obtain ⟨c2,t,e2,h2,bt,zt,f2⟩:=stage cleanup
    (by simp [cleanup,NatAssign.Instruction.Valid,ids,controls]) (Function.update v 1230 (2*q)) B width'
    (by simp [cleanup,NatAssign.Instruction.literalWidth]) input tape b bb zb
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,by rw [cleaned] at bt;exact bt,zt,
    RationalAccumulator.blank_of_eq ((f2.tapes 1249 (by decide)).trans
      ((f1.tapes 1249 (by decide)).trans (f0.tapes 1249 (by decide)))) privateBlank,
    RationalAccumulator.word_of_eq (f2.tapes 1242 (by decide)) cb,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))⟩
  change c0 ≤ 3000*8^2*(B+2)^2 at h0
  change c2 ≤ 3000*8^1*(B+2)^2 at h2
  change c1 ≤ 6*0+15*(2*q).bits.length+21 at h1
  nlinarith only [h0,h1,h2,countWidth]

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathCounter
