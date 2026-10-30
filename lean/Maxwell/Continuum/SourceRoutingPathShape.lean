import Maxwell.Continuum.SourceRoutingPathShapeData

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def shapeCode (shape : Shape) (transpose backwards : Bool) : Code :=
  wordsCode (shape.entries transpose backwards)

theorem shape_executes (shape : Shape) (transpose backwards : Bool)
    (width base B n cursor : ℕ) (clock : List Bool)
    (positive : 0<width) (clockLength : clock.length=width) (room : cursor+3*shape.length ≤ n)
    (v : ℕ→ℕ) (one : v 1219=1) (zero : v 1235=0)
    (bankWidth : ∀j∈GeometryArithmetic.ids,(v j).bits.length ≤ B) (large : 7 ≤ B)
    (fit : ∀axis : Fin 3,(v (axisBank axis)+64).bits.length ≤ width)
    (widthBound : width ≤ B) (baseBound : base.bits.length ≤ B) (sizeBound : n.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (cursorValues v cursor) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : OutputMetadata width base clock s.val) :
    ∃steps t,Executes input tape (shapeCode shape transpose backwards) steps s t ∧
      steps ≤ 2^36*(B+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (cursorValues v (cursor+3*shape.length)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ OutputMetadata width base clock t.val ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+cursor*width)
        (entryBits width v (shape.entries transpose backwards)) ∧ ArchiveFrame wordWork s.val t.val := by
  have literals : ∀e∈shape.entries transpose backwards,e.2.bits.length ≤ B := by
    intro e he
    have h:=Maxwell.Continuum.RationalWords.bits_mono (shape.entry_bound transpose backwards e he)
    have sixtyFour : (64 : ℕ).bits.length=7 := by decide
    rw [sixtyFour] at h
    exact h.trans large
  have fits : ∀e∈shape.entries transpose backwards,(entryValue v e).bits.length ≤ width := by
    intro e he
    exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.add_le_add_left
      (shape.entry_bound transpose backwards e he) (v (axisBank e.1)))).trans (fit e.1)
  obtain ⟨steps,t,he,hc,bt,zt,t1249,mt,memt,ft⟩:=words_executes (shape.entries transpose backwards)
    width base B n cursor clock positive clockLength (by rwa [Shape.entries_length])
    v one zero bankWidth literals fits widthBound baseBound sizeBound input tape s bank ready privateBlank metadata
  refine ⟨steps,t,he,?_,by simpa only [Shape.entries_length] using bt,zt,t1249,mt,memt,ft⟩
  have len:=shape.length_bound
  rw [Shape.entries_length] at hc
  exact hc.trans (Nat.mul_le_mul_right _ (by omega))

#print axioms shape_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
