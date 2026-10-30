import Maxwell.Continuum.SourceRoutingPathPhaseRuntime

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
open Structured Maxwell.Logical.Routing GeometryPath
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

theorem Runtime.step {q : ℕ} {p : Plan q} {initial : SortArrays.Keys q} {start : Port q}
    {level cursor : ℕ} {transpose : Bool} {memory : ℕ→Bool}
    (n : ℕ) (fit : GeometrySort.Fits p.history.width initial)
    (height : level+2*q ≤ 6*q) (capacity : cursor+240*q ≤ n) (i : Fin (2*q))
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : Runtime p initial start level cursor transpose memory i.val s) :
    ∃steps t,Executes input tape (GeometryPath.stepCode transpose) steps s t ∧ steps ≤ 2^244*(p.bound n+3)^2 ∧
      Runtime p initial start level cursor transpose memory (i.val+1) t ∧
      ArchiveFrame footerWork s.val t.val ∧ Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  have nextRoom : cursor+count initial start (i.val+1) ≤ n := by
    have bound:=count_bound initial start (i.val+1)
    have hi:=i.isLt
    omega
  have room : cursor+count initial start i.val+3*length initial start i.val ≤ n := by
    simpa only [count,Nat.add_assoc] using nextRoom
  have currentRoom : cursor+count initial start i.val ≤ n := by omega
  have currentHeight : level+i.val ≤ 6*q := by have hi:=i.isLt;omega
  obtain ⟨steps,t,he,hc,bt,zt,t1249,mt,ot,lt,ct,mem,ft⟩:=GeometryPath.step_executes p.history i.val
    (SortArrays.run initial i.val) (GeometryHistory.run_fits p.history initial fit i.val)
    (finProdFinEquiv (port initial start i.val)) (level+i.val) (cursor+count initial start i.val)
    p.width p.base n p.clock transpose currentHeight p.positive p.clock_length p.coordinate_width
    (by simpa only [Equiv.symm_apply_apply,length] using room)
    input tape s state.bank state.ready state.privateBlank state.metadata state.output state.levelWord state.cursorWord
    (state.stored i.val state.bound)
  have memoryFrame : Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
    rw [mem]
    apply write_frame
    rw [emittedBits_length,Equiv.symm_apply_apply]
    have scaled:=Nat.mul_le_mul_right p.width room
    change (cursor+count initial start i.val)*p.width+3*length initial start i.val*p.width ≤ n*p.width
    nlinarith only [scaled]
  refine ⟨steps,t,he,hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (p.emit_bound i.val (level+i.val) (cursor+count initial start i.val) n
      state.bound currentHeight currentRoom) 3) 2)),
    ⟨i.isLt,?_,zt,t1249,mt,ot,?_,?_,p.history_frame initial n state.stored memoryFrame,?_⟩,ft,memoryFrame⟩
  · simpa only [port,Equiv.symm_apply_apply] using bt
  · simpa only [Nat.add_assoc] using lt
  · simpa only [count,length,Equiv.symm_apply_apply,Nat.add_assoc] using ct
  · rw [mem,state.written]
    exact prefix_extend p initial start level cursor transpose i.val memory

#print axioms Runtime.step
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
