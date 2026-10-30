import Maxwell.Continuum.SourceRoutingPathMovement
import Maxwell.Continuum.SourceRoutingPathCompare
import Maxwell.Continuum.SourceRoutingSortStep

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured Maxwell.Logical.Routing GeometryArithmetic GeometrySort
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def decision {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) : ℕ→ℕ :=
  compareProgram.evaluate (beforeSelect p round saved i)
def decisionCode : Code := .seq partnerProgram.code (.seq readCode compareProgram.code)

theorem decision_flag {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    decision p round saved i 1212=if exchanges round saved (finProdFinEquiv.symm i) then 1 else 0 := by
  rw [decision,compare_result _ (beforeSelect_one p round saved i)]
  have flag : beforeSelect p round saved i 1211=maximumFlag round (finProdFinEquiv.symm i) :=
    congrArg Prod.snd (partner_neighbor i (seed_setup p round i.val))
  simp only [exchanges,flag,SortArrays.keyAt,Equiv.apply_symm_apply]
  rfl

theorem decision_other {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (j : ℕ) (hj : j∉({1212,1222,1223,1224} : Finset ℕ)) :
    decision p round saved i j=beforeSelect p round saved i j :=
  compareProgram.evaluate_other _ j (fun h => hj ((show compareProgram.writes⊆{1212,1222,1223,1224} by decide) h))

theorem decision_cost (B : ℕ) : controlCost compareProgram.steps (2^20*(B+1)) ≤ 2^172*(B+3)^2 := by
  calc
    _ ≤ controlCost 6 (2^20*(B+1)) := controlCost_steps _ _ _ compare_steps
    _ = 2^128*(2^20*(B+1)+2)^2 := rfl
    _ ≤ 2^128*(2^21*(B+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = (2^128*(2^21)^2)*(B+3)^2 := by ring
    _ ≤ 2^172*(B+3)^2 := Nat.mul_le_mul_right _ (by decide)

theorem decision_executes {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (seed p round i.val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (metadata : GeometrySort.Metadata p s.val)
    (source : BitArray.Represents s.val.memory p.source p.width (IncidenceEncoding.words p.width saved)) :
    ∃steps t,Executes input tape decisionCode steps s t ∧ steps ≤ 2^180*(p.bound round+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (decision p round saved i) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata p t.val ∧
      t.val.memory=s.val.memory ∧ ArchiveFrame GeometryArithmetic.work s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,f0⟩:=partner_cost (seed_setup p round i.val) p.positive
    (seed_zero p round i.val) (p.bound round) (by dsimp only [Plan.bound];omega)
    (seed_width p round i.val i.isLt.le) input tape s bank ready privateBlank
  have ma:=metadata.frame (ArchiveFrame.of_binary f0) (by decide)
  obtain ⟨c1,b,e1,h1,bb,zb,b1249,mb,m1,f1⟩:=read_inputs p round saved fit i input tape a ba za a1249 ma
    (by rw [f0.memory];exact source)
  obtain ⟨c2,t,e2,h2,bt,zt,t1249,f2⟩:=compareProgram.executes compare_valid (beforeSelect p round saved i)
    (beforeSelect_zero p round saved i) (compare_admissible _ (beforeSelect_one p round saved i))
    (2^20*(p.bound round+1)) (beforeSelect_width p round saved fit i) (compare_literals _ (by omega))
    input tape b bb zb b1249
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,bt,zt,t1249,
    mb.frame (ArchiveFrame.of_binary f2) (by decide),f2.memory.trans (m1.trans f0.memory),
    (ArchiveFrame.of_binary f0).trans ((f1.mono (by decide)).trans (ArchiveFrame.of_binary f2))⟩
  have first:=h0.trans (Nat.mul_le_mul_left (2^170)
    (Nat.pow_le_pow_left (show p.bound round+2 ≤ p.bound round+3 by omega) 2))
  have last:=h2.trans (decision_cost (p.bound round))
  omega

#print axioms decision_flag
#print axioms decision_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
