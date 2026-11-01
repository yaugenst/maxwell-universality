import Maxwell.Continuum.SourceRoutingPathRestore
import Maxwell.Logical.Routing.SortPaths

/-! Read the stored comparison at the current port and recover its unique
predecessor, then restore the control bank before emitting that strand. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
open Structured GeometryArithmetic GeometryPath GeometrySort Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def predecessorCode : Code := .seq decisionCode (.seq advanceProgram.code
  (.seq (NatAssign.code [.copy 1214 1201]) (NatAssign.code restoreSeed)))

theorem predecessor_executes {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (seed p round i.val) s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (metadata : GeometrySort.Metadata p s.val)
    (source : BitArray.Represents s.val.memory p.source p.width (IncidenceEncoding.words p.width saved)) :
    ∃steps t,Executes input tape predecessorCode steps s t ∧
      steps ≤ 2^188*(p.bound round+3)^2 ∧
      NatAssign.Bank ids (seed p round
        (finProdFinEquiv (RowLayer.destination (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i))).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata p t.val ∧
      t.val.memory=s.val.memory ∧ ArchiveFrame work s.val t.val := by
  let B := 2^34*(p.bound round+3)
  let v := advanced p round saved i
  let next := (finProdFinEquiv
    (RowLayer.destination (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i))).val
  let copied := Function.update v 1201 next
  have copiedValues : NatAssign.values [.copy 1214 1201] v=copied := by
    simp only [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target]
    rw [show v 1214=next from advanced_destination p round saved i]
  have core : ∀j∈seedFields,copied j=seed p round next j := by
    intro j hj
    by_cases same : j=1201
    · subst j; simp [copied,seed]
    have notTemporary : j∉GeometrySort.temporary := by
      simp only [seedFields,Finset.mem_insert,Finset.mem_singleton] at hj
      simp only [GeometrySort.temporary,List.mem_cons,List.not_mem_nil,or_false]
      omega
    have outside : j≠1213 ∧ j≠1214 := by
      simp only [seedFields,Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    rw [show copied j=v j from Function.update_of_ne same _ _,
      show v j=seed p round i.val j from advanced_seed_other p round saved i j notTemporary outside.1 outside.2]
    simp only [seed,same,ite_false]
  have zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,copied j=0 := by
    intro j hj
    have small : j<1200 := by
      simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
        Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    rw [show copied j=v j from Function.update_of_ne (by omega : j≠1201) _ _]
    exact advanced_zero p round saved i j hj
  obtain ⟨c₀,a,e₀,h₀,ba,za,pa,ma,mem₀,f₀⟩ := decision_executes p round saved fit i
    input tape s bank ready privateBlank metadata source
  obtain ⟨c₁,b,e₁,h₁,bb,zb,pb,f₁⟩ := advance_executes p round saved fit i input tape a ba za pa
  obtain ⟨c₂,c,e₂,h₂,bc,zc,f₂⟩ := stage [.copy 1214 1201]
    (by simp [NatAssign.Instruction.Valid,ids,controls]) v B (advanced_width p round saved fit i)
    (by simp [NatAssign.Instruction.literalWidth]) input tape b bb zb
  have copiedWidth : ∀j∈ids,(copied j).bits.length ≤ 2*B+1 := by
    have h := NatAssign.instruction_width ids (.copy 1214 1201)
      (by simp [NatAssign.Instruction.Valid,ids,controls]) v B
      (advanced_width p round saved fit i) (by simp [NatAssign.Instruction.literalWidth])
    simpa only [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      show v 1214=next from advanced_destination p round saved i] using h
  obtain ⟨c₃,t,e₃,h₃,bt,zt,pt,f₃⟩ := restoreSeed_executes p round next (2*B+1) copied core zero
    copiedWidth input tape c (by rwa [copiedValues] at bc) zc
    (RationalAccumulator.blank_of_eq (f₂.tapes 1249 (by decide)) pb)
  have frame := f₀.trans ((ArchiveFrame.of_binary f₁).trans
    ((ArchiveFrame.of_binary (f₂.mono (by
      intro j hj
      simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
      tauto))).trans (ArchiveFrame.of_binary f₃)))
  refine ⟨c₀+(c₁+(c₂+c₃)),t,e₀.seq (e₁.seq (e₂.seq e₃)),?_,bt,zt,pt,
    metadata.frame frame (by decide),f₃.memory.trans (f₂.memory.trans (f₁.memory.trans mem₀)),frame⟩
  have copyCost : c₂ ≤ 2^86*(p.bound round+3)^2 := calc
    c₂ ≤ 3000*8^1*(B+2)^2 := h₂
    _ ≤ 3000*8^1*(2^35*(p.bound round+3))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [B];omega) 2)
    _ ≤ 2^86*(p.bound round+3)^2 := by nlinarith
  have restoreCost : c₃ ≤ 2^182*(p.bound round+3)^2 := calc
    c₃ ≤ 2^110*(2*B+1+2)^2 := h₃
    _ ≤ 2^110*(2^36*(p.bound round+3))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [B];omega) 2)
    _ = 2^182*(p.bound round+3)^2 := by ring
  omega

#print axioms predecessor_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
