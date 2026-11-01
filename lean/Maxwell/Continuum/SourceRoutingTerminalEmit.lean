import Maxwell.Continuum.SourceRoutingTerminalData
import Maxwell.Continuum.SourceRoutingPathReverseFooter

/-! Terminal preparation, literal emission, and cleanup form one fixed machine.
The result restores the saved routing seed and advances only the output cursor. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def terminalCode (bottom : Bool) (choice : ShapeChoice) (backwards : Bool) : Code :=
  .seq (terminalPrepare bottom) (.seq (choice.code false backwards) GeometryPathReverse.footerCode)

def terminalWork : Finset ℕ := {1253}∪wordWork

def terminalBound {q : ℕ} (p : GeometrySort.Plan q) (round width base n : ℕ) : ℕ :=
  p.bound round+width+base.bits.length+n.bits.length+16

theorem terminal_executes {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q)
    (bottom : Bool) (choice : ShapeChoice) (valid : choice.Valid) (depth : choice.depth ≤ 2) (backwards : Bool)
    (cursor width base n : ℕ) (clock : List Bool)
    (positive : 0<width) (clockLength : clock.length=width)
    (coordinateWidth : (1024*q+1).bits.length ≤ width) (room : cursor+192 ≤ n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed p round (finProdFinEquiv port).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometrySort.Metadata p s.val) (output : OutputMetadata width base clock s.val)
    (cursorWord : Word s.val 1253 cursor) :
    let v := terminalValues p round port cursor bottom
    let shape := choice.evaluate v
    ∃steps t,Executes input tape (terminalCode bottom choice backwards) steps s t ∧
      steps ≤ 2^142*(terminalBound p round width base n+3)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed p round (finProdFinEquiv port).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata p t.val ∧
      OutputMetadata width base clock t.val ∧ Word t.val 1253 (cursor+3*shape.length) ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+cursor*width)
        (entryBits width v (shape.entries false backwards)) ∧
      ArchiveFrame terminalWork s.val t.val ∧
      Tree.Memory.Frame base (n*width) s.val.memory t.val.memory := by
  dsimp only
  let B := terminalBound p round width base n
  let v := terminalValues p round port cursor bottom
  let shape := choice.evaluate v
  let next := cursor+3*shape.length
  have pb : p.bound round ≤ B := by dsimp only [B,terminalBound];omega
  have wb : width ≤ B := by dsimp only [B,terminalBound];omega
  have bb : base.bits.length ≤ B := by dsimp only [B,terminalBound];omega
  have nb : n.bits.length ≤ B := by dsimp only [B,terminalBound];omega
  have large : 7 ≤ B := by dsimp only [B,terminalBound];omega
  have cb : cursor.bits.length ≤ B := (Maxwell.Continuum.RationalWords.bits_mono (show cursor ≤ n by omega)).trans nb
  have fitsRoom : next ≤ n := by
    have h := shape.length_bound
    dsimp only [next]
    omega
  have nextBound : next.bits.length ≤ B := (Maxwell.Continuum.RationalWords.bits_mono fitsRoom).trans nb
  have wide : B ≤ 2^9*(B+1) := by omega
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,f₀⟩ := terminalPrepare_executes p round port cursor B bottom large pb cb
    input tape s bank ready privateBlank cursorWord
  have sameCursor : cursorValues v cursor=v := Function.update_eq_self_iff.mpr (terminal_cursor p round port cursor bottom).symm
  have bankA : NatAssign.Bank ids (cursorValues v cursor) a.val := by rw [sameCursor];exact ba
  have widthA := terminal_width p round port cursor B bottom large pb cb
  have fa : ArchiveFrame wordWork s.val a.val := (ArchiveFrame.of_binary f₀).mono Finset.subset_union_right
  obtain ⟨c₁,b,e₁,h₁,bbank,zb,pbBlank,ob,mb,f₁⟩ := choice.executes valid false backwards
    width base (2^9*(B+1)) n cursor clock positive clockLength v fitsRoom
    (terminal_one p round port cursor bottom) (terminal_scratch_zero p round port cursor bottom)
    widthA (by omega) (terminal_coordinates_fit p round port cursor width bottom coordinateWidth)
    (wb.trans wide) (bb.trans wide) (nb.trans wide) input tape a bankA za pa (output.frame fa)
  let out := cursorValues v next
  have fields : ∀j∈seedFields,out j=GeometrySort.seed p round (finProdFinEquiv port).val j := by
    intro j hj
    have distinct : j≠1234 := by simp only [seedFields,Finset.mem_insert,Finset.mem_singleton] at hj;omega
    change cursorValues v next j=_
    rw [cursorValues_other _ _ _ distinct]
    exact terminal_fields p round port cursor bottom j hj
  have zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,out j=0 := by
    intro j hj
    have small : j<1200 := by
      simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    change cursorValues v next j=0
    rw [cursorValues_other v next j (by omega)]
    exact terminal_zero p round port cursor bottom j hj
  have widthB : ∀j∈ids,(out j).bits.length ≤ 2^9*(B+1) :=
    cursorValues_width _ _ _ widthA (nextBound.trans wide)
  obtain ⟨c₂,t,e₂,h₂,bt,zt,pt,ct,f₂⟩ := GeometryPathReverse.footer_executes p round
    (finProdFinEquiv port).val cursor (2^9*(B+1)) out fields zero widthB (cb.trans wide)
    input tape b bbank zb pbBlank
    (RationalAccumulator.word_of_eq ((f₁.tapes 1253 (by decide) (by decide)).trans
      (f₀.tapes 1253 (by decide))) cursorWord)
  have frame : ArchiveFrame terminalWork s.val t.val :=
    ((fa.trans f₁).mono Finset.subset_union_right).trans ((ArchiveFrame.of_binary f₂).mono (by decide))
  have written : t.val.memory=MemoryWord.writeBits s.val.memory (base+cursor*width)
      (entryBits width v (shape.entries false backwards)) := by rw [f₂.memory,mb,f₀.memory]
  refine ⟨c₀+(c₁+c₂),t,e₀.seq (e₁.seq e₂),?_,bt,zt,pt,metadata.frame frame (by decide),
    ⟨RationalAccumulator.word_of_eq (f₂.tapes 1250 (by decide)) ob.wordWidth,
      RationalAccumulator.word_of_eq (f₂.tapes 1252 (by decide)) ob.baseWord,
      BankArray.word_of_eq (f₂.tapes 1251 (by decide)) ob.clockWord⟩,
    ct,written,frame,?_⟩
  · have square : (2^9*(B+1)+3)^2 ≤ (2^10*(B+3))^2 := Nat.pow_le_pow_left (by omega) 2
    have bound₁ : c₁ ≤ 2^58*(B+3)^2 := by
      have scaled := Nat.mul_le_mul_left (2^36) square
      have normal : 2^36*(2^10*(B+3))^2=2^56*(B+3)^2 := by ring
      rw [normal] at scaled
      nlinarith only [h₁,scaled,depth]
    have bound₂ : c₂ ≤ 2^132*(B+3)^2 := calc
      c₂ ≤ 2^112*(2^9*(B+1)+2)^2 := h₂
      _ ≤ 2^112*(2^10*(B+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = 2^132*(B+3)^2 := by ring
    change c₀+(c₁+c₂) ≤ 2^142*(B+3)^2
    have bound₀ := h₀.trans (Nat.mul_le_mul_left (2^139) (Nat.pow_le_pow_left (show B+2 ≤ B+3 by omega) 2))
    omega
  · rw [written]
    apply GeometryPathPhase.write_frame
    have size : (entryBits width v (shape.entries false backwards)).length=3*shape.length*width := by
      rw [entryBits_length,Shape.entries_length]
    rw [size,←Nat.add_mul]
    exact Nat.mul_le_mul_right width fitsRoom

#print axioms terminal_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
