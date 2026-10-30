import Maxwell.Continuum.SourceRoutingPathEmit
import Maxwell.Continuum.SourceRoutingHistoryLayout

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

def nextTemporary : List ℕ :=
  [1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1218,
    1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239]

def nextAssignments : List NatAssign.Instruction :=
  [.copy 1214 1201,.copy 1200 1225,.multiply 1200 1225,.multiply 1217 1225,
    .copy 1216 1215,.add 1225 1216,.add 1219 1202]

def nextCleanup : List NatAssign.Instruction := nextAssignments++NatAssign.clearList nextTemporary

structure NextFields {q : ℕ} (p : GeometryHistory.Plan q) (k next : ℕ) (v : ℕ→ℕ) : Prop where
  count : v 1200=q
  round : v 1202=k+1
  source : v 1215=p.slab k
  destination : v 1216=p.slab (k+1)
  width : v 1217=p.width
  one : v 1219=1
  two : v 1220=2
  nextPort : v 1214=next
  quotient : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0

theorem nextCleanup_valid : ∀a∈nextCleanup,a.Valid ids := by
  simp [nextCleanup,nextAssignments,nextTemporary,NatAssign.clearList,NatAssign.Instruction.Valid,ids,controls]

theorem nextCleanup_values {q : ℕ} (p : GeometryHistory.Plan q) (k next : ℕ) (v : ℕ→ℕ)
    (fields : NextFields p k next v) (j : ℕ) (hj : j∈ids) :
    NatAssign.values nextCleanup v j=GeometrySort.seed (p.layer (k+1)) (k+2) next j := by
  rw [nextCleanup,Maxwell.Continuum.RationalDataflow.values_append,NatAssign.clearList_values]
  by_cases temporary : j∈nextTemporary
  · rw [ite_eq_left temporary]
    have outside : j≠1200 ∧ j≠1201 ∧ j≠1202 ∧ j≠1215 ∧ j≠1216 ∧ j≠1217 ∧ j≠1219 ∧ j≠1220 := by
      simp only [nextTemporary,List.mem_cons,List.not_mem_nil,or_false] at temporary
      omega
    simp only [GeometrySort.seed,outside.1,outside.2.1,outside.2.2.1,outside.2.2.2.1,
      outside.2.2.2.2.1,outside.2.2.2.2.2.1,outside.2.2.2.2.2.2.1,outside.2.2.2.2.2.2.2,ite_false]
  · rw [ite_eq_right temporary]
    have cases : j=1200 ∨ j=1201 ∨ j=1202 ∨ j=1215 ∨ j=1216 ∨ j=1217 ∨ j=1219 ∨ j=1220 ∨
        j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts := by
      simp only [ids,controls,Finset.mem_union,Finset.mem_Icc] at hj
      simp only [nextTemporary,List.mem_cons,List.not_mem_nil,or_false,not_or] at temporary
      rcases hj with hj|hj
      · omega
      · tauto
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|natural
    all_goals simp only [nextAssignments,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target]
    · simp [fields.count,GeometrySort.seed]
    · simp [fields.nextPort,GeometrySort.seed]
    · simp [fields.one,fields.round,GeometrySort.seed];omega
    · simp [fields.destination,GeometrySort.seed,GeometryHistory.Plan.layer]
    · simp [fields.width,fields.count,fields.destination,GeometrySort.seed,
        GeometryHistory.Plan.layer,GeometryHistory.Plan.slab,GeometryHistory.Plan.stride,GeometryHistory.Plan.width];ring
    · simp [fields.width,GeometrySort.seed,GeometryHistory.Plan.width,GeometrySort.Plan.width]
    · simp [fields.one,GeometrySort.seed]
    · simp [fields.two,GeometrySort.seed]
    · have small : j<1200 := by
        simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
          Finset.mem_insert,Finset.mem_singleton] at natural
        omega
      simp only [Function.update_of_ne (show j≠1202 by omega),Function.update_of_ne (show j≠1216 by omega),
        Function.update_of_ne (show j≠1215 by omega),Function.update_of_ne (show j≠1225 by omega),
        Function.update_of_ne (show j≠1201 by omega),fields.quotient j natural]
      simp only [GeometrySort.seed,show j≠1200 by omega,show j≠1201 by omega,show j≠1202 by omega,
        show j≠1215 by omega,show j≠1216 by omega,show j≠1217 by omega,show j≠1219 by omega,show j≠1220 by omega,ite_false]

theorem nextCleanup_executes {q : ℕ} (p : GeometryHistory.Plan q) (k next B : ℕ) (v : ℕ→ℕ)
    (fields : NextFields p k next v) (width : ∀j∈ids,(v j).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (bank : NatAssign.Bank ids v s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : RationalAccumulator.Blank s.val 1249) :
    ∃steps t,Executes input tape (NatAssign.code nextCleanup) steps s t ∧ steps ≤ 2^132*(B+2)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed (p.layer (k+1)) (k+2) next) t.val ∧
      GeometryArray.Ready t.val ∧ RationalAccumulator.Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨steps,t,he,hc,bt,zt,ft⟩:=stage nextCleanup nextCleanup_valid v B width
    (by simp [nextCleanup,nextAssignments,nextTemporary,NatAssign.clearList,NatAssign.Instruction.literalWidth]) input tape s bank ready
  refine ⟨steps,t,he,?_,?_,zt,RationalAccumulator.blank_of_eq (ft.tapes 1249 (by decide)) privateBlank,ft.mono ?_⟩
  · exact hc.trans (Nat.mul_le_mul_right _ (by decide))
  · intro j hj
    rw [←nextCleanup_values p k next v fields j hj]
    exact bt j hj
  · intro j hj
    simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto

#print axioms nextCleanup_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
