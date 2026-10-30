import Maxwell.Continuum.SourceRoutingPathDecision

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured Maxwell.Logical.Routing GeometryArithmetic GeometrySort
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem decision_direction {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    decision p round saved i 1211=maximumFlag round (finProdFinEquiv.symm i) :=
  (decision_other p round saved i 1211 (by decide)).trans
    (congrArg Prod.snd (partner_neighbor i (seed_setup p round i.val)))

theorem decision_neighbor {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    decision p round saved i 1210=(neighbor round i).val :=
  (decision_other p round saved i 1210 (by decide)).trans
    (congrArg Prod.fst (partner_neighbor i (seed_setup p round i.val)))

theorem decision_column {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    decision p round saved i 1203=i.val/q := by
  rw [decision_other p round saved i 1203 (by decide)]
  change partnerProgram.evaluate (seed p round i.val) 1203=i.val/q
  rw [program_evaluate,choosePartner.evaluate_other _ _ (by decide)]
  exact (prepared_fields (seed_setup p round i.val)).2.1

theorem decision_row {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    decision p round saved i 1204=i.val%q := by
  rw [decision_other p round saved i 1204 (by decide)]
  change partnerProgram.evaluate (seed p round i.val) 1204=i.val%q
  rw [program_evaluate,choosePartner.evaluate_other _ _ (by decide)]
  exact (prepared_fields (seed_setup p round i.val)).2.2.1

theorem decision_cursor {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    decision p round saved i 1201=i.val :=
  (decision_other p round saved i 1201 (by decide)).trans (intermediate_other p round i 1201 (by decide))

theorem decision_right_positive {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (positive : 0<decision p round saved i 1211) : 0<decision p round saved i 1203 := by
  rw [decision_direction,maximumFlag] at positive
  rw [decision_column]
  split_ifs at positive with hl hr
  · omega
  · exact hr.1
  · omega

theorem decision_zero {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,decision p round saved i j=0 :=
  compareProgram.evaluate_zero compare_valid (beforeSelect p round saved i) (beforeSelect_zero p round saved i)

private theorem width_arithmetic (B : ℕ) : 2^6*(2^20*(B+1)+1) ≤ 2^27*(B+3) := by omega

theorem decision_width {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) :
    ∀j∈GeometryArithmetic.ids,(decision p round saved i j).bits.length ≤ 2^27*(p.bound round+3) := by
  have h:=compareProgram.evaluate_width compare_valid (beforeSelect p round saved i)
    (2^20*(p.bound round+1)) (beforeSelect_width p round saved fit i) (compare_literals _ (by omega))
  intro j hj
  have actual:=(Nat.le_add_right _ _).trans (h j hj)
  have hstep:=Nat.mul_le_mul_right (2^20*(p.bound round+1)+1)
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) compare_steps)
  exact actual.trans (hstep.trans (width_arithmetic (p.bound round)))

#print axioms decision_right_positive
#print axioms decision_width
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
