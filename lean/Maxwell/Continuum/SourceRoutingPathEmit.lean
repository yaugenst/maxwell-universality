import Maxwell.Continuum.SourceRoutingPathCoordinates

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic GeometrySort Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def emitBound {q : ℕ} (p : Plan q) (round level cursor width base n : ℕ) : ℕ :=
  prepareBound p round level cursor+width+base.bits.length+n.bits.length+16

def emitCode (transpose : Bool) : Code :=
  .seq decisionCode (.seq (prepareCode transpose) (rowChoice.code transpose false))

def emittedBits {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor width : ℕ) (transpose : Bool) : List Bool :=
  entryBits width (emissionValues p round saved i level cursor transpose)
    ((moveShape (RowLayer.movement (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i))).entries transpose false)

theorem emit_executes {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (level cursor width base n : ℕ) (clock : List Bool)
    (transpose : Bool) (levelBound : level ≤ 6*q) (widthPositive : 0<width) (clockLength : clock.length=width)
    (coordinateWidth : (1024*q+1).bits.length ≤ width)
    (room : cursor+3*RowLayer.pathLength (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) ≤ n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (seed p round i.val) s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (metadata : GeometrySort.Metadata p s.val)
    (output : OutputMetadata width base clock s.val) (levelWord : Word s.val 1255 level) (cursorWord : Word s.val 1253 cursor)
    (source : BitArray.Represents s.val.memory p.source p.width (IncidenceEncoding.words p.width saved)) :
    ∃steps t,Executes input tape (emitCode transpose) steps s t ∧
      steps ≤ 2^226*(emitBound p round level cursor width base n+3)^2 ∧
      NatAssign.Bank ids (cursorValues (emissionValues p round saved i level cursor transpose)
        (cursor+3*RowLayer.pathLength (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i))) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata p t.val ∧ OutputMetadata width base clock t.val ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+cursor*width) (emittedBits p round saved i level cursor width transpose) ∧
      ArchiveFrame wordWork s.val t.val := by
  let B:=emitBound p round level cursor width base n
  let v:=emissionValues p round saved i level cursor transpose
  have prep : prepareBound p round level cursor ≤ B := by dsimp only [B,emitBound];omega
  have pb : p.bound round ≤ B := by dsimp only [B,emitBound,prepareBound];omega
  have wb : width ≤ B := by dsimp only [B,emitBound];omega
  have bb : base.bits.length ≤ B := by dsimp only [B,emitBound];omega
  have nb : n.bits.length ≤ B := by dsimp only [B,emitBound];omega
  have wide : B ≤ 2^49*(B+3) := by omega
  obtain ⟨c0,a,e0,h0,ba,za,a1249,_,m0,f0⟩:=decision_executes p round saved fit i input tape s bank ready privateBlank metadata source
  obtain ⟨c1,b,e1,h1,bbank,zb,b1249,f1⟩:=prepare_executes p round saved fit i level cursor transpose input tape a ba za a1249
    (RationalAccumulator.word_of_eq (f0.tapes 1255 (by decide) (by decide)) levelWord)
    (RationalAccumulator.word_of_eq (f0.tapes 1253 (by decide) (by decide)) cursorWord)
  have firstFrame : ArchiveFrame wordWork s.val b.val :=
    (f0.mono Finset.subset_union_right).trans ((ArchiveFrame.of_binary f1).mono Finset.subset_union_right)
  have sameCursor : cursorValues v cursor=v :=
    Function.update_eq_self_iff.mpr (emission_cursor p round saved i level cursor transpose).symm
  have bbank' : NatAssign.Bank ids (cursorValues v cursor) b.val := by rw [sameCursor];exact bbank
  have length : (rowChoice.evaluate v).length=RowLayer.pathLength (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i) := by
    rw [emission_choice,moveShape_length]
  obtain ⟨c2,t,e2,h2,bt,zt,t1249,mt,memt,ft⟩:=rowChoice.executes rowChoice_valid transpose false width base
    (2^49*(B+3)) n cursor clock widthPositive clockLength v (by rwa [length])
    (emission_one p round saved i level cursor transpose) (emission_scratch_zero p round saved i level cursor transpose)
    (fun j hj => (emission_width p round saved fit i level cursor transpose j hj).trans
      (Nat.mul_le_mul_left _ (by omega))) (by omega)
    (emission_coordinates_fit p round saved i level cursor width transpose levelBound coordinateWidth)
    (wb.trans wide) (bb.trans wide) (nb.trans wide) input tape b bbank' zb b1249 (output.frame firstFrame)
  have frame:=firstFrame.trans ft
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,by simpa only [length] using bt,zt,t1249,
    metadata.frame frame (by decide),mt,?_,frame⟩
  · have d0:=h0.trans (Nat.mul_le_mul_left (2^180) (Nat.pow_le_pow_left (show p.bound round+3 ≤ B+3 by omega) 2))
    have d1:=h1.trans (Nat.mul_le_mul_left (2^224) (Nat.pow_le_pow_left (show prepareBound p round level cursor+3 ≤ B+3 by omega) 2))
    have d2 : c2 ≤ 2^140*(B+3)^2 := by
      rw [rowChoice_depth] at h2
      have square:=Nat.mul_le_mul_left (2^36) (Nat.pow_le_pow_left (show 2^49*(B+3)+3 ≤ 2^50*(B+3) by omega) 2)
      have normal : 2^36*(2^50*(B+3))^2=2^136*(B+3)^2 := by ring
      rw [normal] at square
      nlinarith only [h2,square]
    change c0+(c1+c2) ≤ 2^226*(B+3)^2
    omega
  · rw [memt,f1.memory,m0,emission_choice]
    rfl

#print axioms emit_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
