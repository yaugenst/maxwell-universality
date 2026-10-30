import Maxwell.Continuum.SourceRoutingPathChoiceData

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem ShapeChoice.executes (choice : ShapeChoice) (valid : choice.Valid) (transpose backwards : Bool)
    (width base B n cursor : ℕ) (clock : List Bool)
    (positive : 0<width) (clockLength : clock.length=width) (v : ℕ→ℕ)
    (room : cursor+3*(choice.evaluate v).length ≤ n) (one : v 1219=1) (zero : v 1235=0)
    (bankWidth : ∀j∈GeometryArithmetic.ids,(v j).bits.length ≤ B) (large : 7 ≤ B)
    (fit : ∀axis : Fin 3,(v (axisBank axis)+64).bits.length ≤ width)
    (widthBound : width ≤ B) (baseBound : base.bits.length ≤ B) (sizeBound : n.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (cursorValues v cursor) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : OutputMetadata width base clock s.val) :
    ∃steps t,Executes input tape (choice.code transpose backwards) steps s t ∧
      steps ≤ 2^36*(B+3)^2+4*choice.depth ∧
      NatAssign.Bank GeometryArithmetic.ids (cursorValues v (cursor+3*(choice.evaluate v).length)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ OutputMetadata width base clock t.val ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+cursor*width)
        (entryBits width v ((choice.evaluate v).entries transpose backwards)) ∧ ArchiveFrame wordWork s.val t.val := by
  induction choice generalizing s with
  | shape value =>
    simpa only [ShapeChoice.code,ShapeChoice.depth,ShapeChoice.evaluate,Nat.mul_zero,Nat.add_zero] using
      shape_executes value transpose backwards width base B n cursor clock positive clockLength room
        v one zero bankWidth large fit widthBound baseBound sizeBound input tape s bank ready privateBlank metadata
  | positive source yes no iy ino =>
    let a:=positiveState source s
    have ea:=positive_executes source input tape s
    have sourceWord : RationalAccumulator.Word s.val source (v source) := by
      simpa only [cursorValues_other v cursor source valid.2.1] using
        bank source (Finset.mem_union_left _ valid.1)
    have flag:=positive_flag source (v source) s sourceWord
    have za : GeometryArray.Ready a.val := ⟨ready.scratch,ready.seven,ready.pack⟩
    have frame : ArchiveFrame wordWork s.val a.val :=
      (ArchiveFrame.of_binary (positive_frame source s)).mono Finset.subset_union_right
    by_cases hp : 0<v source
    · have selected : ShapeChoice.evaluate (.positive source yes no) v=yes.evaluate v := by
        simp only [ShapeChoice.evaluate,hp,ite_true]
      rw [selected] at room ⊢
      obtain ⟨cost,t,he,hc,bt,zt,t1249,mt,memt,ft⟩:=iy valid.2.2.1 room a bank za privateBlank (metadata.frame frame)
      have hf : a.val.registers 23=true := by simpa only [hp,decide_true] using flag
      refine ⟨3+(1+cost),t,ea.seq (Executes.yes hf he),?_,bt,zt,t1249,mt,memt,frame.trans ft⟩
      change 3+(1+cost) ≤ 2^36*(B+3)^2+4*(1+max yes.depth no.depth)
      have depth:=le_max_left yes.depth no.depth
      omega
    · have selected : ShapeChoice.evaluate (.positive source yes no) v=no.evaluate v := by
        simp only [ShapeChoice.evaluate,hp,ite_false]
      rw [selected] at room ⊢
      obtain ⟨cost,t,he,hc,bt,zt,t1249,mt,memt,ft⟩:=ino valid.2.2.2 room a bank za privateBlank (metadata.frame frame)
      have hf : a.val.registers 23=false := by simpa only [hp,decide_false] using flag
      refine ⟨3+(1+cost),t,ea.seq (Executes.no hf he),?_,bt,zt,t1249,mt,memt,frame.trans ft⟩
      change 3+(1+cost) ≤ 2^36*(B+3)^2+4*(1+max yes.depth no.depth)
      have depth:=le_max_right yes.depth no.depth
      omega

#print axioms ShapeChoice.executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
