import Maxwell.Continuum.SourceRoutingPhaseReads
import Maxwell.Continuum.SourceRoutingPhaseStore
import Maxwell.Continuum.SourceRoutingPhaseArithmetic
import Maxwell.Continuum.NatAssignOutputWidth

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
open Structured Maxwell.Logical.Routing GeometryArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem before_width {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q)
    (colors : RowColoring target) (i : Fin (q*q)) :
    ∀j∈GeometryArithmetic.ids,(beforeArithmetic p colors i j).bits.length ≤ p.bound := by
  intro j hj
  by_cases h3 : j=1203
  · subst j
    simpa only [beforeArithmetic,Function.update_self] using (target_fit p target i).trans p.width_bound
  · by_cases h2 : j=1202
    · subst j
      simpa only [beforeArithmetic,afterLabels,Function.update_of_ne h3,Function.update_self] using
        (label_fit p colors i).trans p.width_bound
    · simpa only [beforeArithmetic,afterLabels,Function.update_of_ne h3,Function.update_of_ne h2] using
        seed_width p i.val i.isLt.le j hj

theorem before_zero {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q)
    (colors : RowColoring target) (i : Fin (q*q)) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,beforeArithmetic p colors i j=0 := by
  intro j hj
  have different : j≠1203 ∧ j≠1202 := by
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  simpa only [beforeArithmetic,afterLabels,Function.update_of_ne different.1,
    Function.update_of_ne different.2] using seed_zero p i.val j hj

theorem before_positive {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q)
    (colors : RowColoring target) (i : Fin (q*q)) : 0<beforeArithmetic p colors i 1200 := p.positive

theorem encoded_quotient {q : ℕ} (p : Port q) : (finProdFinEquiv p).val/q=p.1.val :=
  congrArg (fun a : Port q => a.1.val) (finProdFinEquiv.symm_apply_apply p)
theorem encoded_remainder {q : ℕ} (p : Port q) : (finProdFinEquiv p).val%q=p.2.val :=
  congrArg (fun a : Port q => a.2.val) (finProdFinEquiv.symm_apply_apply p)

theorem output_writes {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q)
    (colors : RowColoring target) (i : Fin (q*q)) :
    Writes p colors i (output (beforeArithmetic p colors i)) := by
  have label : beforeArithmetic p colors i 1202=q*(colors.color (port i)).val := label_value colors i
  have targetAt : beforeArithmetic p colors i 1203=(finProdFinEquiv (target (port i))).val := target_value target i
  have divisor : beforeArithmetic p colors i 1200=q := rfl
  have sourceAt : beforeArithmetic p colors i 1201=i.val := rfl
  have colorAt : output (beforeArithmetic p colors i) 1204=(colors.color (port i)).val := by
    rw [color,label,divisor,Nat.mul_div_right _ p.positive]
  refine ⟨rfl,?_,?_,colorAt,?_,?_,rfl,rfl,rfl⟩
  · rw [middleIndex,divisor,sourceAt,label,Nat.mul_div_right _ p.positive]
    exact (PhaseKeys.middleAddress_value colors (port i)).symm
  · rw [lastIndex,label,targetAt,divisor,encoded_remainder]
    exact (PhaseKeys.lastAddress_value colors (port i)).symm
  · rw [targetRow,targetAt,divisor,encoded_remainder]
    rfl
  · rw [targetColumn,targetAt,divisor,encoded_quotient]
    rfl

theorem output_width {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q)
    (colors : RowColoring target) (i : Fin (q*q)) :
    ∀j∈GeometryArithmetic.ids,(output (beforeArithmetic p colors i) j).bits.length ≤ 32*(p.bound+1) := by
  have w0:=divided_width (beforeArithmetic p colors i) 1202 1200 1204 1205 p.bound
    (by decide) (before_width p colors i)
  have w1:=divided_width (firstDivision (beforeArithmetic p colors i)) 1203 1200 1206 1207 p.bound
    (by decide) w0
  have w2:=divided_width (secondDivision (beforeArithmetic p colors i)) 1201 1200 1208 1209 p.bound
    (by decide) w1
  have h:=NatAssign.values_width_bound GeometryArithmetic.ids finish finish_valid
    (thirdDivision (beforeArithmetic p colors i)) p.bound w2
    (by simp [finish,NatAssign.Instruction.literalWidth])
  intro j hj
  exact (Nat.le_add_right _ _).trans (h j hj)

#print axioms output_writes
#print axioms output_width
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
