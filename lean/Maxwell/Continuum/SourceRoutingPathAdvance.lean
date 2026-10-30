import Maxwell.Continuum.SourceRoutingPathFields

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured Maxwell.Logical.Routing GeometryArithmetic GeometrySort
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def nextPort : Control := .positive 1212 (.assign (.copy 1210 1214) .done) .done
def lowerPort : Control := .positive 1211 (.decrement 1213 nextPort) nextPort
def advanceProgram : Control := Control.prepend [.copy 1203 1213,.copy 1201 1214] lowerPort
def advanced {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) : ℕ→ℕ :=
  advanceProgram.evaluate (decision p round saved i)

theorem advance_valid : advanceProgram.Valid := by
  simp [advanceProgram,lowerPort,nextPort,Control.Valid,Control.prepend,NatAssign.Instruction.Valid,controls]
theorem advance_steps : advanceProgram.steps ≤ 6 := by decide
theorem advance_literals (B : ℕ) : advanceProgram.Literals B := by
  simp [advanceProgram,lowerPort,nextPort,Control.Literals,Control.prepend,NatAssign.Instruction.literalWidth]
theorem advance_admissible (v : ℕ→ℕ) (positive : 0<v 1211→0<v 1203) : advanceProgram.Admissible v := by
  simp only [advanceProgram,lowerPort,nextPort,Control.Admissible,Control.prepend,List.foldr_cons,List.foldr_nil,
    NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
    Function.update_self,Function.update_of_ne (by decide : (1211 : ℕ)≠1214),
    Function.update_of_ne (by decide : (1211 : ℕ)≠1213),
    Function.update_of_ne (by decide : (1213 : ℕ)≠1214)]
  split_ifs <;> simp_all

theorem advance_result (v : ℕ→ℕ) :
    advanceProgram.evaluate v 1213=(if 0<v 1211 then v 1203-1 else v 1203) ∧
      advanceProgram.evaluate v 1214=(if 0<v 1212 then v 1210 else v 1201) := by
  by_cases direction : 0<v 1211 <;> by_cases exchange : 0<v 1212 <;>
    simp [advanceProgram,lowerPort,nextPort,Control.evaluate,Control.prepend,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,direction,exchange]

theorem advanced_lower {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    advanced p round saved i 1213=lower round (finProdFinEquiv.symm i) := by
  rw [advanced,(advance_result _).1,decision_direction,decision_column]
  rfl

theorem advanced_destination {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    advanced p round saved i 1214=
      (finProdFinEquiv (RowLayer.destination (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i))).val := by
  rw [advanced,(advance_result _).2,decision_flag,decision_neighbor,decision_cursor,destination_eq]
  by_cases h : exchanges round saved (finProdFinEquiv.symm i)
  · simp only [h,ite_true,show (0 : ℕ)<1 by decide]
    rfl
  · simp only [h,ite_false,show ¬(0 : ℕ)<0 by decide,Equiv.apply_symm_apply]

theorem advanced_other {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (j : ℕ) (hj : j≠1213 ∧ j≠1214) : advanced p round saved i j=decision p round saved i j :=
  advanceProgram.evaluate_other _ j (by
    intro h
    have member:=(show advanceProgram.writes⊆{1213,1214} by decide) h
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    exact member.elim hj.1 hj.2)

theorem advance_cost (B : ℕ) : controlCost advanceProgram.steps (2^27*(B+3)) ≤ 2^184*(B+3)^2 := by
  calc
    _ ≤ controlCost 6 (2^27*(B+3)) := controlCost_steps _ _ _ advance_steps
    _ = 2^128*(2^27*(B+3)+2)^2 := rfl
    _ ≤ 2^128*(2^28*(B+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = 2^184*(B+3)^2 := by ring

theorem advance_executes {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (decision p round saved i) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape advanceProgram.code steps s t ∧ steps ≤ 2^184*(p.bound round+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (advanced p round saved i) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame GeometryArithmetic.work s.val t.val := by
  obtain ⟨steps,t,he,hc,bt,zt,t1249,ft⟩:=advanceProgram.executes advance_valid (decision p round saved i)
    (decision_zero p round saved i) (advance_admissible _ (decision_right_positive p round saved i))
    (2^27*(p.bound round+3)) (decision_width p round saved fit i) (advance_literals _)
    input tape s bank ready privateBlank
  exact ⟨steps,t,he,hc.trans (advance_cost _),bt,zt,t1249,ft⟩

#print axioms advanced_destination
#print axioms advance_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
