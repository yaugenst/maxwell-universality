import Maxwell.Continuum.SourceRoutingPathHeaderCount
import Maxwell.Continuum.SourceRoutingPathPhaseMemory
import Maxwell.Cost.Structured.CounterClear

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def headerCode : Code := .seq headerCountCode
  (.seq (BankArray.writeCanonicalCode 1250 1256 1252 1251 1232)
    (.seq (NatAssign.code restoreSeed) (.call (TapeOps.clear 1256))))

def headerWork : Finset ℕ := {1256}∪wordWork

/-- Backpatch the reserved length word after an actual path traversal. The
count is recovered from the two machine cursors, and the saved cursor is erased. -/
theorem header_executes {q : ℕ} (p : GeometrySort.Plan q) (round index : ℕ)
    (indexBound : index ≤ q*q) (start length width base n B : ℕ) (clock : List Bool)
    (large : 7 ≤ B) (planBound : p.bound round ≤ B) (widthBound : width ≤ B)
    (baseBound : base.bits.length ≤ B) (nextBound : (start+1+3*length).bits.length ≤ B)
    (positive : 0<width) (clockLength : clock.length=width)
    (lengthFit : length.bits.length ≤ width) (room : start<n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed p round index) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (output : OutputMetadata width base clock s.val)
    (startWord : Word s.val 1256 start) (nextWord : Word s.val 1253 (start+1+3*length)) :
    ∃steps t,Executes input tape headerCode steps s t ∧ steps ≤ 2^113*(B+3)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed p round index) t.val ∧ GeometryArray.Ready t.val ∧
      Blank t.val 1249 ∧ OutputMetadata width base clock t.val ∧ Blank t.val 1256 ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+start*width) (IncidenceEncoding.word width length) ∧
      ArchiveFrame headerWork s.val t.val ∧ Tree.Memory.Frame base (n*width) s.val.memory t.val.memory := by
  let v:=GeometrySort.seed p round index
  let out:=headerCountValues v start (start+1+3*length)
  have startBound : start.bits.length ≤ B :=
    (Maxwell.Continuum.RationalWords.bits_mono (by omega : start ≤ start+1+3*length)).trans nextBound
  have vw : ∀j∈ids,(v j).bits.length ≤ B := fun j hj =>
    (GeometrySort.seed_width p round index indexBound j hj).trans planBound
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,f₀⟩:=headerCount_executes v start (start+1+3*length) B
    (by omega) (by omega) vw startBound nextBound (GeometrySort.seed_zero p round index)
    (by simp [v,GeometrySort.seed]) input tape s bank ready privateBlank startWord nextWord
  have aoutput : OutputMetadata width base clock a.val :=
    ⟨RationalAccumulator.word_of_eq (f₀.tapes 1250 (by decide)) output.wordWidth,
      RationalAccumulator.word_of_eq (f₀.tapes 1252 (by decide)) output.baseWord,
      BankArray.word_of_eq (f₀.tapes 1251 (by decide)) output.clockWord⟩
  have astart : Word a.val 1256 start:=RationalAccumulator.word_of_eq (f₀.tapes 1256 (by decide)) startWord
  have alength : Word a.val 1232 length := by
    simpa only [headerCount_value] using ba 1232 (by decide)
  let old:=GeometryArray.snapshot a.val.memory base width n
  obtain ⟨c₁,b,e₁,h₁,bb,zb,pb,mb,_,f₁⟩:=GeometryArithmetic.write 1250 1256 1252 1251 1232
    (by decide) (by decide) (by decide) (by decide) (by decide) width base B length clock old
    ⟨start,room⟩ positive clockLength lengthFit widthBound startBound baseBound input tape out a ba za pa
    aoutput.wordWidth astart aoutput.baseWord aoutput.clockWord alength
    (GeometryArray.snapshot_represents _ _ _ _)
  have fields : ∀j∈seedFields,out j=GeometrySort.seed p round index j := by
    intro j hj
    have h : j≠1230 ∧ j≠1231 ∧ j≠1232 ∧ j≠1233 := by
      simp only [seedFields,Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    exact headerCount_other _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2
  have zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,out j=0 := by
    intro j hj
    have small : j<1200 := by
      simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
        Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    change headerCountValues v start (start+1+3*length) j=0
    rw [headerCount_other _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
    exact GeometrySort.seed_zero p round index j hj
  have outWidth:=headerCount_width v start (start+1+3*length) B (by omega) vw nextBound
  obtain ⟨c₂,c,e₂,h₂,bc,zc,pc,f₂⟩:=restoreSeed_executes p round index B out fields zero outWidth
    input tape b bb zb pb
  have cstart : Word c.val 1256 start:=RationalAccumulator.word_of_eq
    ((f₂.tapes 1256 (by decide)).trans (f₁.tapes 1256 (by decide) (by decide))) astart
  obtain ⟨origin,originWord⟩:=cstart
  obtain ⟨t,e₃,zt,f₃⟩:=RuntimeCounter.clear_executes 1256 input tape start.bits origin c originWord
  have ft : ArchiveFrame headerWork s.val t.val :=
    (((ArchiveFrame.of_binary f₀).mono (by
      intro j hj;exact Finset.mem_union_right _ (Finset.mem_union_right _ hj))).trans
      (f₁.mono (by simp [headerWork,wordWork]))).trans
      (((ArchiveFrame.of_binary f₂).mono (by
        intro j hj;exact Finset.mem_union_right _ (Finset.mem_union_right _ hj))).trans
        ((ArchiveFrame.of_binary f₃).mono Finset.subset_union_left))
  have memory : t.val.memory=MemoryWord.writeBits s.val.memory (base+start*width)
      (IncidenceEncoding.word width length) := by rw [f₃.memory,f₂.memory,mb,f₀.memory]
  refine ⟨c₀+(c₁+(c₂+(6*start.bits.length+4))),t,e₀.seq (e₁.seq (e₂.seq e₃)),?_,
    bank_of_frame bc f₃ (by decide),zc.of_tapes (fun j hj => f₃.tapes j (by simp only [Finset.mem_singleton];omega)),
    RationalAccumulator.blank_of_eq (f₃.tapes 1249 (by decide)) pc,?_,zt,memory,ft,?_⟩
  · have h₀': c₀ ≤ 2^103*(B+3)^2:=h₀.trans (by gcongr;omega)
    have h₂': c₂ ≤ 2^110*(B+3)^2:=h₂.trans (by gcongr;omega)
    nlinarith only [h₀',h₁,h₂',startBound]
  · exact ⟨RationalAccumulator.word_of_eq (ft.tapes 1250 (by decide) (by decide)) output.wordWidth,
      RationalAccumulator.word_of_eq (ft.tapes 1252 (by decide) (by decide)) output.baseWord,
      BankArray.word_of_eq (ft.tapes 1251 (by decide) (by decide)) output.clockWord⟩
  · rw [memory]
    apply GeometryPathPhase.write_frame
    simp only [IncidenceEncoding.word,FixedWidth.bits_length]
    have bound:=Nat.mul_le_mul_right width (show start+1 ≤ n by omega)
    simpa only [Nat.add_mul,one_mul] using bound

#print axioms header_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
