import Maxwell.Continuum.SourceRoutingTraversalState
import Maxwell.Continuum.SourceRoutingLevelCost

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 512

def bodyCost (heap rows total : ℕ) : ℕ :=
  Level.upperCost (2^total) (2^(total+rows)) (Level.uniformWidth (width heap rows total))

theorem State.step (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (setup : Setup v heap rows total) (d : ℕ) (hd : d<total-1)
    (input : List Bool) (tape : ℕ→Bool) (start : BitRAMState) (s : Store)
    (hs : State v heap rows total root d start s) :
    ∃steps t,Executes input tape Level.nextCode steps s t ∧ steps ≤ bodyCost heap rows total ∧
      State v heap rows total root (d+1) start t ∧ t.val.tapes 830=s.val.tapes 830 := by
  let columns:=total-(d+2)
  let L:=width heap rows total
  let current:=values v d
  have hcol : total-(d+1)=columns+1 := by dsimp only [columns];omega
  have parentCol : total-d=columns+1+1 := by dsimp only [columns];omega
  let target:=Targets.level rows total (d+1) (columns+1) root hcol
  have hL : 1 ≤ L := by dsimp only [L,width,Level.uniformWidth];omega
  have hn : 2*(2*2^(columns+rows)) ≤ 2^(total+rows) := by
    rw [←pow_succ',←pow_succ']
    apply Nat.pow_le_pow_right (by decide)
    dsimp only [columns];omega
  have hw : columns+rows+3 ≤ total+rows+1 := by dsimp only [columns];omega
  have coords:=visit_coordinates v heap (2^(total+rows)) (total+rows+1) rows total setup.coordinates d (by omega)
  have hz:=quotient_zero v setup.zero d
  have hv:=words v heap rows total setup.coordinates setup.population setup.words d (by omega)
  have hp : (2^(d+1)).bits.length ≤ L :=
    (ControllerWidth.population_width heap (2^(total+rows)) (total+rows+1) total (d+1) (by omega)).trans
      (by dsimp only [L,width,Level.uniformWidth];omega)
  have pop:=population v setup.population setup.coordinates.two d
  let p:=Level.ofCoordinates rows columns d heap (2^(total+rows)) (total+rows+1) L current target
    hL hn hw coords hz hv hp
  have parents:=hs.outputs d (by omega) (columns+1) parentCol
  have inputs : p.Inputs s.val.memory := by
    have it:=Level.inputs_from_parents rows columns d heap (2^(total+rows)) (total+rows+1) L current
      (Targets.level rows total d (columns+1+1) root parentCol) hL hn hw coords hz hv hp s.val.memory parents
    have targets:=Targets.level_next rows total d columns root parentCol
    rw [←targets] at it
    exact it
  obtain ⟨steps,t,he,hcost,bt,zt,t839,t831,done,ft,mt⟩:=Level.next_executes rows columns d heap
    (2^(total+rows)) (total+rows+1) L current target hL hn hw coords hz hv hp pop.1 input tape s
    hs.bank hs.clean hs.scratch hs.counter inputs
  have complete:=Level.completed_outputs rows columns d heap (2^(total+rows)) (total+rows+1) L current target
    hL hn hw coords hz hv hp t.val.memory done
  have completedPrefix : Prefix heap rows total root (d+1+1) t.val.memory :=
    (hs.outputs.preserve mt).append hcol complete
  have memory:=hs.memory.trans (memory_widen heap rows total (d+1) (2^(d+1)) (by omega) le_rfl _ _ mt)
  refine ⟨steps,t,he,?_,⟨bt,zt,t839,t831,completedPrefix,hs.frame.trans (Frame.of_level ft),memory⟩,
    ft.tapes 830 (by omega) (by omega) (by decide) (by decide) (by omega)⟩
  let B:=Level.uniformWidth L
  have widen : L ≤ B := (Nat.le_add_right L 2).trans
    (Nat.le_mul_of_pos_left (L+2) (by decide : 0<2^30))
  have hbits : (2^(d+1)).bits.length ≤ B := hp.trans widen
  have nodes : (2 : ℕ)^(d+1) ≤ 2^total := Nat.pow_le_pow_right (by decide)
    (Nat.succ_le_of_lt (lt_of_lt_of_le hd (Nat.sub_le total 1)))
  have count : 2*2^(columns+rows) ≤ 2^(total+rows) :=
    (Nat.le_mul_of_pos_left (2*2^(columns+rows)) (by decide : 0<2)).trans hn
  change steps ≤ Level.wholeCost p at hcost
  change steps ≤ Level.upperCost (2^total) (2^(total+rows)) p.B
  exact hcost.trans (Level.wholeCost_bound p (2^total) (2^(total+rows)) nodes count hbits)

#print axioms State.step
end Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
