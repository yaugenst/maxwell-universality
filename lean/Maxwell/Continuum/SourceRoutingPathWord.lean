import Maxwell.Continuum.SourceRoutingPathWordValues
import Maxwell.Continuum.SourceRoutingTreeMemory

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem word_executes {n : ℕ} (axis : Fin 3) (offset width base B : ℕ) (clock : List Bool)
    (old : Vector (List Bool) n) (i : Fin n) (positive : 0<width) (clockLength : clock.length=width)
    (v : ℕ→ℕ) (cursor : v 1234=i.val) (one : v 1219=1) (zero : v 1235=0)
    (bankWidth : ∀j∈GeometryArithmetic.ids,(v j).bits.length ≤ B) (literal : offset.bits.length ≤ B)
    (fit : (v (axisBank axis)+offset).bits.length ≤ width)
    (widthBound : width ≤ B) (baseBound : base.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (metadata : OutputMetadata width base clock s.val)
    (stored : BitArray.Represents s.val.memory base width old) :
    ∃steps t,Executes input tape (wordCode axis offset) steps s t ∧ steps ≤ 2^28*(B+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (Function.update v 1234 (i.val+1)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ OutputMetadata width base clock t.val ∧
      BitArray.Represents t.val.memory base width
        (old.set i (IncidenceEncoding.word width (v (axisBank axis)+offset))) ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+i.val*width)
        (IncidenceEncoding.word width (v (axisBank axis)+offset)) ∧ ArchiveFrame wordWork s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,za,f0⟩:=stage (wordPrepare axis offset) (wordPrepare_valid axis offset) v B bankWidth
    (by simp [wordPrepare,NatAssign.Instruction.literalWidth,literal]) input tape s bank ready
  have smallWork : ({0,1,2,3}∪GeometryArithmetic.ids : Finset ℕ)⊆wordWork := by
    intro j hj
    simp only [wordWork,GeometryArithmetic.work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto
  have ma:=metadata.frame ((ArchiveFrame.of_binary f0).mono smallWork)
  have ai : RationalAccumulator.Word a.val 1234 i.val := by
    simpa only [wordPrepare_values,Function.update_of_ne (by decide : (1234 : ℕ)≠1235),cursor] using ba 1234 (by decide)
  have av : RationalAccumulator.Word a.val 1235 (v (axisBank axis)+offset) := by
    simpa only [wordPrepare_values,Function.update_self] using ba 1235 (by decide)
  obtain ⟨c1,b,e1,h1,bb,zb,b1249,m1,sb,f1⟩:=GeometryArithmetic.write
    1250 1234 1252 1251 1235 (by decide) (by decide) (by decide) (by decide) (by decide)
    width base B (v (axisBank axis)+offset) clock old i positive clockLength fit widthBound
    (by simpa only [cursor] using bankWidth 1234 (by decide)) baseBound input tape
    (NatAssign.values (wordPrepare axis offset) v) a ba za
    (RationalAccumulator.blank_of_eq (f0.tapes 1249 (by decide)) privateBlank)
    ma.wordWidth ai ma.baseWord ma.clockWord av (by rw [f0.memory];exact stored)
  obtain ⟨c2,t,e2,h2,bt,zt,f2⟩:=stage wordCleanup wordCleanup_valid
    (NatAssign.values (wordPrepare axis offset) v) (4*(B+1))
    (wordPrepare_width axis offset v B bankWidth literal)
    (by simp [wordCleanup,NatAssign.Instruction.literalWidth]) input tape b bb zb
  have frame : ArchiveFrame wordWork s.val t.val :=
    ((ArchiveFrame.of_binary f0).mono smallWork).trans
      ((f1.mono Finset.subset_union_left).trans ((ArchiveFrame.of_binary f2).mono smallWork))
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,?_,zt,
    RationalAccumulator.blank_of_eq (f2.tapes 1249 (by decide)) b1249,metadata.frame frame,
    by rw [f2.memory];exact sb,by rw [f2.memory,m1,f0.memory],frame⟩
  · change c0 ≤ 3000*8^2*(B+2)^2 at h0
    change c2 ≤ 3000*8^2*(4*(B+1)+2)^2 at h2
    nlinarith
  · simpa only [wordCleanup_values axis offset v one zero,cursor] using bt

#print axioms word_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
