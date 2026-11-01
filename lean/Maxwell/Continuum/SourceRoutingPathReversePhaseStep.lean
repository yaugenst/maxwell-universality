import Maxwell.Continuum.SourceRoutingPathReverseRuntime

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
open Structured GeometryPath GeometryPathPhase Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

theorem Runtime.step {q : ℕ} {p : Plan q} {initial : SortArrays.Keys q} {start : Port q}
    {level cursor : ℕ} {transpose : Bool} {memory : ℕ→Bool}
    (n : ℕ) (fit : GeometrySort.Fits p.history.width initial)
    (height : level+2*q ≤ 6*q) (capacity : cursor+240*q ≤ n) (i : Fin (2*q))
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : Runtime p initial start level cursor transpose memory i.val s) :
    ∃steps t,Executes input tape (stepCode transpose) steps s t ∧ steps ≤ 2^234*(p.bound n+3)^2 ∧
      Runtime p initial start level cursor transpose memory (i.val+1) t ∧
      ArchiveFrame stepWork s.val t.val ∧ Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  let k := 2*q-(i.val+1)
  have remaining : k+1=2*q-i.val := by dsimp only [k];have := i.isLt;omega
  have bounded : k+1 ≤ 2*q := by dsimp only [k];have := i.isLt;omega
  have previous : RowLayer.destination (SortArrays.arraySelection (k+1) (SortArrays.run initial k))
      (port initial start (k+1))=port initial start k := SortPaths.port_reverse_step initial start k
  have nextRoom : cursor+reverseCount initial start (2*q) (i.val+1) ≤ n := by
    have bound := reverseCount_bound initial start (2*q) (i.val+1)
    have hi := i.isLt
    omega
  have room : cursor+reverseCount initial start (2*q) i.val+3*length initial start k ≤ n := by
    simpa only [reverseCount,Nat.add_assoc] using nextRoom
  have currentRoom : cursor+reverseCount initial start (2*q) i.val ≤ n := by omega
  have currentHeight : level+k ≤ 6*q := by omega
  have inputBank : NatAssign.Bank GeometryArithmetic.ids
      (GeometrySort.seed (p.history.layer (k+1)) (k+2) (finProdFinEquiv (port initial start (k+1))).val) s.val := by
    simpa only [show k+2=(k+1)+1 by omega,remaining] using state.bank
  have inputMetadata : GeometrySort.Metadata (p.history.layer (k+1)) s.val := by
    simpa only [remaining] using state.metadata
  have inputLevel : RationalAccumulator.Word s.val 1255 (level+k+1) := by
    simpa only [Nat.add_assoc,remaining] using state.levelWord
  obtain ⟨steps,t,he,hc,bt,zt,pt,mt,ot,lt,ct,mem,ft⟩ := step_executes p.history k
    (SortArrays.run initial k) (GeometryHistory.run_fits p.history initial fit k)
    (port initial start (k+1)) (level+k) (cursor+reverseCount initial start (2*q) i.val)
    p.width p.base n p.clock transpose currentHeight p.positive p.clock_length p.coordinate_width
    (by simpa only [previous,length] using room) input tape s inputBank state.ready state.privateBlank
    inputMetadata state.output inputLevel state.cursorWord (state.stored k (by omega))
  simp only [previous] at bt ct mem
  have memoryFrame : Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
    rw [mem]
    apply GeometryPathPhase.write_frame
    rw [emittedBits_length (backwards := true),Equiv.symm_apply_apply]
    have scaled := Nat.mul_le_mul_right p.width room
    change (cursor+reverseCount initial start (2*q) i.val)*p.width+3*length initial start k*p.width ≤ n*p.width
    nlinarith only [scaled]
  have cost : steps ≤ 2^234*(p.bound n+3)^2 := by
    have emit := p.emit_bound k (level+k) (cursor+reverseCount initial start (2*q) i.val) n
      (by omega) currentHeight currentRoom
    have history : (p.history.layer (k+1)).bound (k+2) ≤ p.history.bound := by
      simpa only [Nat.add_assoc] using p.history.layer_bound (k+1) bounded
    have levelWidth := Maxwell.Continuum.RationalWords.bits_mono (show level+k+1 ≤ 6*q+1 by omega)
    have bound : stepBound p.history k (level+k) (cursor+reverseCount initial start (2*q) i.val)
        p.width p.base n ≤ 3*p.bound n := by
      dsimp only [stepBound,Plan.bound] at *
      omega
    calc
      steps ≤ 2^230*(stepBound p.history k (level+k) (cursor+reverseCount initial start (2*q) i.val)
          p.width p.base n+3)^2 := hc
      _ ≤ 2^230*(4*(p.bound n+3))^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = 2^234*(p.bound n+3)^2 := by ring
  refine ⟨steps,t,he,cost,⟨i.isLt,bt,zt,pt,mt,ot,lt,?_,
    p.history_frame initial n state.stored memoryFrame,?_⟩,ft,memoryFrame⟩
  · simpa only [reverseCount,length,Nat.add_assoc] using ct
  · rw [mem,state.written]
    exact prefix_extend p initial start level cursor transpose i.val memory

#print axioms Runtime.step
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
