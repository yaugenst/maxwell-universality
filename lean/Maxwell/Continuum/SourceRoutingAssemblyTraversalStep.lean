import Maxwell.Continuum.SourceRoutingAssemblyTraversalState
import Maxwell.Continuum.SourceRoutingAssemblyLevelCost

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 512

def bodyCost (heap rows total : ℕ) : ℕ :=
  AssemblyLevel.upperCost (2^total) (2^(total+rows)) (AssemblyLevel.uniformWidth (width heap rows total))

theorem State.step (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (setup : Setup v heap rows total) (r : ℕ) (hr : r<total)
    (input : List Bool) (tape : ℕ→Bool) (start : BitRAMState) (s : Store)
    (hs : State v heap rows total root r start s) :
    ∃steps t,Executes input tape AssemblyLevel.nextCode steps s t ∧ steps ≤ bodyCost heap rows total ∧
      State v heap rows total root (r+1) start t ∧ t.val.tapes 830=s.val.tapes 830 := by
  let d:=total-(r+1)
  let L:=width heap rows total
  let current:=values v total r
  have hcol : total-d=r+1 := by dsimp only [d];omega
  let target:=Targets.level rows total d (r+1) root hcol
  have hL : 2 ≤ L := by dsimp only [L,width,AssemblyLevel.uniformWidth];omega
  have hn : 2*2^(r+rows) ≤ 2^(total+rows) := by
    rw [←pow_succ']
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hw : r+rows+2 ≤ total+rows+1 := by omega
  have coords:=coordinates v heap (2^(total+rows)) (total+rows+1) rows total setup.coordinates r hr
  have hz:=quotient_zero v total setup.zero r
  have hv:=words v heap rows total setup.coordinates setup.population setup.words r (Nat.le_of_lt hr)
  have hp : (2^d).bits.length ≤ L :=
    (ControllerWidth.population_width heap (2^(total+rows)) (total+rows+1) total d (by dsimp only [d];omega)).trans
      (by dsimp only [L,width,baseWidth,AssemblyLevel.uniformWidth];omega)
  have pop:=population v total setup.population setup.coordinates.two r hr
  let p : AssemblyLevel.Plan rows r d :=
    ⟨heap,2^(total+rows),total+rows+1,current,L,hL,hn,hw,coords,hz,hv,hp,target⟩
  have inputs : p.Inputs 0 s.val.memory := by
    intro i _
    have colors:=hs.outputs d (by dsimp only [d];omega) r hcol i
    refine ⟨colors,?_⟩
    intro b
    have labels:=hs.labels (d+1) (by dsimp only [d];omega) (Targets.child d i b)
    rw [Targets.heap_child,Targets.level_child rows total d r root hcol i b] at labels
    exact labels
  obtain ⟨steps,t,he,hcost,bt,zt,t839,t831,done,ft,mt⟩:=
    AssemblyLevel.next_executes p pop.1 input tape s hs.bank hs.clean hs.scratch hs.counter inputs
  have earlier : Traversal.Prefix heap rows total root d s.val.memory := by
    intro q hq columns hc i
    exact hs.outputs q (by dsimp only [d] at hq;omega) columns hc i
  have completedPrefix:=earlier.preserve mt
  have frontier : Frontier heap rows total root (r+1) t.val.memory := by
    intro q hq i
    have heq : q=d := by dsimp only [d];omega
    subst q
    exact done i i.isLt
  have memory:=hs.memory.trans (Traversal.memory_widen heap rows total d (2^d)
    (by dsimp only [d];omega) le_rfl _ _ mt)
  refine ⟨steps,t,he,?_,⟨bt,zt,t839,t831,completedPrefix,frontier,
    hs.frame.trans (Traversal.Frame.of_level ft),memory⟩,
    ft.tapes 830 (by omega) (by omega) (by decide) (by decide) (by omega)⟩
  have hbits : (2^d).bits.length ≤ AssemblyLevel.uniformWidth L := hp.trans (by
    dsimp only [AssemblyLevel.uniformWidth];omega)
  have nodes : (2 : ℕ)^d ≤ 2^total := Nat.pow_le_pow_right (by decide) (by dsimp only [d];omega)
  change steps ≤ AssemblyLevel.upperCost (2^total) (2^(total+rows)) (AssemblyLevel.uniformWidth p.L)
  exact hcost.trans (AssemblyLevel.wholeCost_bound p (2^total) (2^(total+rows)) nodes hn hbits)

#print axioms State.step
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
