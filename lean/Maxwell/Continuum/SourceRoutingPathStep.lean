import Maxwell.Continuum.SourceRoutingPathFooter

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic GeometrySort Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def stepCode (transpose : Bool) : Code := .seq (emitCode transpose) footerCode

private theorem step_width_arithmetic (P B : ℕ) (bound : P ≤ B) : 2^49*(P+3) ≤ 2^50*(B+3) := by omega

theorem emittedBits_length {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor width : ℕ) (transpose : Bool) :
    (emittedBits p round saved i level cursor width transpose).length=
      3*RowLayer.pathLength (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i)*width := by
  rw [emittedBits,entryBits_length,Shape.entries_length,moveShape_length]

theorem step_executes {q : ℕ} (p : GeometryHistory.Plan q) (k : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (level cursor width base n : ℕ) (clock : List Bool)
    (transpose : Bool) (levelBound : level ≤ 6*q) (widthPositive : 0<width) (clockLength : clock.length=width)
    (coordinateWidth : (1024*q+1).bits.length ≤ width)
    (room : cursor+3*RowLayer.pathLength (SortArrays.arraySelection (k+1) saved) (finProdFinEquiv.symm i) ≤ n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (seed (p.layer k) (k+1) i.val) s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (metadata : GeometrySort.Metadata (p.layer k) s.val)
    (output : OutputMetadata width base clock s.val) (levelWord : Word s.val 1255 level) (cursorWord : Word s.val 1253 cursor)
    (source : BitArray.Represents s.val.memory (p.slab k) p.width (IncidenceEncoding.words p.width saved)) :
    ∃steps t,Executes input tape (stepCode transpose) steps s t ∧
      steps ≤ 2^244*(emitBound (p.layer k) (k+1) level cursor width base n+3)^2 ∧
      NatAssign.Bank ids (seed (p.layer (k+1)) (k+2)
        (finProdFinEquiv (RowLayer.destination (SortArrays.arraySelection (k+1) saved) (finProdFinEquiv.symm i))).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata (p.layer (k+1)) t.val ∧ OutputMetadata width base clock t.val ∧
      Word t.val 1255 (level+1) ∧
      Word t.val 1253 (cursor+3*RowLayer.pathLength (SortArrays.arraySelection (k+1) saved) (finProdFinEquiv.symm i)) ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+cursor*width)
        (emittedBits (p.layer k) (k+1) saved i level cursor width transpose) ∧ ArchiveFrame footerWork s.val t.val := by
  let B:=emitBound (p.layer k) (k+1) level cursor width base n
  let nextCursor:=cursor+3*RowLayer.pathLength (SortArrays.arraySelection (k+1) saved) (finProdFinEquiv.symm i)
  let v:=cursorValues (emissionValues (p.layer k) (k+1) saved i level cursor transpose) nextCursor
  obtain ⟨c0,a,e0,h0,ba,za,a1249,ma,oa,mem,fa⟩:=emit_executes (p.layer k) (k+1) saved fit i level cursor width base n
    clock transpose levelBound widthPositive clockLength coordinateWidth room input tape s bank ready privateBlank metadata output levelWord cursorWord source
  have nb : n.bits.length ≤ B := by dsimp only [B,emitBound];omega
  have cb : cursor.bits.length ≤ B := (Maxwell.Continuum.RationalWords.bits_mono (show cursor ≤ n by omega)).trans nb
  have nextBound : nextCursor.bits.length ≤ B := (Maxwell.Continuum.RationalWords.bits_mono room).trans nb
  have vb : ∀j∈ids,(v j).bits.length ≤ 2^50*(B+3) := by
    apply cursorValues_width
    · intro j hj
      have h:=emission_width (p.layer k) (k+1) saved fit i level cursor transpose j hj
      have small : prepareBound (p.layer k) (k+1) level cursor ≤ B := by dsimp only [B,emitBound];omega
      exact h.trans (step_width_arithmetic _ B small)
    · omega
  obtain ⟨c1,t,e1,h1,bt,zt,t1249,ct,lt,ft⟩:=footer_executes p k _ level cursor (2^50*(B+3)) v
    (nextFields_emission p k saved i level cursor nextCursor transpose)
    (by dsimp only [v];rw [cursorValues_other _ _ 1233 (by decide)];exact emission_level _ _ _ _ _ _ _)
    vb (by omega) input tape a ba za a1249
    (RationalAccumulator.word_of_eq (fa.tapes 1253 (by decide) (by decide)) cursorWord)
    (RationalAccumulator.word_of_eq (fa.tapes 1255 (by decide) (by decide)) levelWord)
  have totalFrame : ArchiveFrame footerWork s.val t.val :=
    (fa.mono Finset.subset_union_right).trans (ArchiveFrame.of_binary ft)
  have finalMetadata:=metadata.frame totalFrame (by decide)
  refine ⟨c0+c1,t,e0.seq e1,?_,bt,zt,t1249,⟨finalMetadata.width,finalMetadata.clock⟩,
    ⟨RationalAccumulator.word_of_eq (ft.tapes 1250 (by decide)) oa.wordWidth,
      RationalAccumulator.word_of_eq (ft.tapes 1252 (by decide)) oa.baseWord,
      BankArray.word_of_eq (ft.tapes 1251 (by decide)) oa.clockWord⟩,
    lt,ct,ft.memory.trans mem,totalFrame⟩
  have last : c1 ≤ 2^242*(B+3)^2 := calc
    c1 ≤ 2^140*(2^50*(B+3)+3)^2 := h1
    _ ≤ 2^140*(2^51*(B+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = 2^242*(B+3)^2 := by ring
  change c0+c1 ≤ 2^244*(B+3)^2
  change c0 ≤ 2^226*(B+3)^2 at h0
  omega

#print axioms step_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
