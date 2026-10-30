import Maxwell.Continuum.SourceRoutingSortPartnerMeaning

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def left {q : ℕ} (parity : ℕ) (p : Port q) : Prop := p.1.val+1<q ∧ (p.1.val+1)%2=parity%2
def right {q : ℕ} (parity : ℕ) (p : Port q) : Prop := 0<p.1.val ∧ p.1.val%2=parity%2
instance {q : ℕ} (parity : ℕ) (p : Port q) : Decidable (left parity p) := inferInstanceAs (Decidable (_∧_))
instance {q : ℕ} (parity : ℕ) (p : Port q) : Decidable (right parity p) := inferInstanceAs (Decidable (_∧_))

def neighborPort {q : ℕ} (parity : ℕ) (p : Port q) : Port q :=
  if hl : left parity p then (⟨p.1.val+1,hl.1⟩,p.2)
  else if right parity p then (⟨p.1.val-1,(Nat.sub_le _ _).trans_lt p.1.isLt⟩,p.2) else p
def maximumFlag {q : ℕ} (parity : ℕ) (p : Port q) : ℕ :=
  if left parity p then 0 else if right parity p then 1 else 0
def neighbor {q : ℕ} (parity : ℕ) (i : Fin (q*q)) : Fin (q*q) :=
  finProdFinEquiv (neighborPort parity (finProdFinEquiv.symm i))

theorem neighbor_value {q : ℕ} (parity : ℕ) (i : Fin (q*q)) :
    (neighbor parity i).val=
      if left parity (finProdFinEquiv.symm i) then i.val+q
      else if right parity (finProdFinEquiv.symm i) then q*(i.val/q-1)+i.val%q else i.val := by
  unfold neighbor neighborPort
  split_ifs
  · change i.val%q+q*(i.val/q+1)=i.val+q
    have h:=Nat.mod_add_div i.val q
    rw [Nat.mul_add,Nat.mul_one]
    omega
  · exact Nat.add_comm _ _
  · exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)

theorem partner_neighbor {q round : ℕ} (i : Fin (q*q)) {v : ℕ→ℕ}
    (setup : PartnerSetup q i.val round v) :
    (partnerProgram.evaluate v 1210,partnerProgram.evaluate v 1211)=
      ((neighbor round i).val,maximumFlag round (finProdFinEquiv.symm i)) := by
  rw [partner_result setup,neighbor_value]
  have col : (finProdFinEquiv.symm i : Port q).1.val=i.val/q := rfl
  by_cases same : (i.val/q)%2=round%2
  · have notLeft : ¬left round (finProdFinEquiv.symm i) := by
      simp only [left,col]
      omega
    simp only [same,ite_true,maximumFlag,notLeft,ite_false,right,col]
    by_cases positive : 0 < i.val/q <;> simp [positive]
  · have next : (i.val/q+1)%2=round%2 := by omega
    have notRight : ¬right round (finProdFinEquiv.symm i) := by simp only [right,col,same,and_false,not_false_eq_true]
    simp only [same,ite_false,maximumFlag,notRight,left,col,next,and_true]
    by_cases room : i.val/q+1<q <;> simp [room]

theorem step_neighbor {q : ℕ} (parity : ℕ) (saved : SortArrays.Keys q) (p : Port q) :
    SortArrays.keyAt (SortArrays.step parity saved) p=
      if 0<maximumFlag parity p then
        max (SortArrays.keyAt saved p) (SortArrays.keyAt saved (neighborPort parity p))
      else min (SortArrays.keyAt saved p) (SortArrays.keyAt saved (neighborPort parity p)) := by
  have cLeft : SortArrays.center q parity (p.1.val+1)=decide (left parity p) := by
    apply decide_eq_decide.mpr
    dsimp only [left]
    omega
  have cRight : SortArrays.center q parity p.1.val=decide (right parity p) := by
    apply decide_eq_decide.mpr
    dsimp only [right]
    have := p.1.isLt
    omega
  simp only [SortArrays.keyAt,SortArrays.step,SortArrays.get_ofFn,Equiv.symm_apply_apply,cLeft,cRight]
  by_cases hl : left parity p
  · have room:=hl.1
    simp [hl,maximumFlag,neighborPort,SortArrays.word,SortArrays.keyAt,p.1.isLt,p.2.isLt,room]
  · by_cases hr : right parity p
    · have predRoom : p.1.val-1<q := (Nat.sub_le _ _).trans_lt p.1.isLt
      simp [hl,hr,maximumFlag,neighborPort,SortArrays.word,SortArrays.keyAt,
        p.1.isLt,p.2.isLt,predRoom,max_comm]
    · simp [hl,hr,maximumFlag,neighborPort,SortArrays.word,SortArrays.keyAt,p.1.isLt,p.2.isLt]

theorem step_value {q : ℕ} (parity : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    (SortArrays.step parity saved).get i=
      if 0<maximumFlag parity (finProdFinEquiv.symm i) then max (saved.get i) (saved.get (neighbor parity i))
      else min (saved.get i) (saved.get (neighbor parity i)) := by
  have h:=step_neighbor parity saved (finProdFinEquiv.symm i)
  simpa only [SortArrays.keyAt,Equiv.apply_symm_apply,neighbor] using h

#print axioms partner_neighbor
#print axioms step_value
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
