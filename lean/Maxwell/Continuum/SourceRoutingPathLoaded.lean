import Maxwell.Continuum.SourceRoutingPathPiece
import Maxwell.Continuum.SourceRoutingCopyWord

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic GeometrySort Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def pathLoaded (v : ℕ→ℕ) (level cursor : ℕ) : ℕ→ℕ :=
  Function.update (Function.update v 1233 level) 1234 cursor

def emissionValues {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) : ℕ→ℕ :=
  (originProgram transpose).evaluate (pathLoaded (advanced p round saved i) level cursor)

theorem pathLoaded_other (v : ℕ→ℕ) (level cursor j : ℕ) (h33 : j≠1233) (h34 : j≠1234) :
    pathLoaded v level cursor j=v j := by simp only [pathLoaded,Function.update_of_ne h33,Function.update_of_ne h34]

private theorem advanced_width_arithmetic (B : ℕ) : 2^6*(2^27*(B+3)+1) ≤ 2^34*(B+3) := by omega

theorem advanced_width {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) :
    ∀j∈GeometryArithmetic.ids,(advanced p round saved i j).bits.length ≤ 2^34*(p.bound round+3) := by
  have h:=advanceProgram.evaluate_width advance_valid (decision p round saved i) (2^27*(p.bound round+3))
    (decision_width p round saved fit i) (advance_literals _)
  intro j hj
  have power:=Nat.mul_le_mul_right (2^27*(p.bound round+3)+1)
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) advance_steps)
  exact (Nat.le_add_right _ _).trans ((h j hj).trans (power.trans (advanced_width_arithmetic _)))

theorem advanced_zero {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,advanced p round saved i j=0 :=
  advanceProgram.evaluate_zero advance_valid _ (decision_zero p round saved i)

theorem advanced_seed_other {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (i : Fin (q*q)) (j : ℕ) (hj : j∉GeometrySort.temporary) (h13 : j≠1213) (h14 : j≠1214) :
    advanced p round saved i j=seed p round i.val j :=
  (advanced_other p round saved i j ⟨h13,h14⟩).trans (decision_seed_other p round saved i j hj)

theorem pathLoaded_width (v : ℕ→ℕ) (level cursor B : ℕ)
    (bankWidth : ∀j∈ids,(v j).bits.length ≤ B) (levelWidth : level.bits.length ≤ B) (cursorWidth : cursor.bits.length ≤ B) :
    ∀j∈ids,(pathLoaded v level cursor j).bits.length ≤ B := by
  intro j hj
  by_cases h34 : j=1234
  · subst j;exact cursorWidth
  by_cases h33 : j=1233
  · subst j;simpa only [pathLoaded,Function.update_of_ne h34,Function.update_self] using levelWidth
  simpa only [pathLoaded_other v level cursor j h33 h34] using bankWidth j hj

theorem pathLoaded_zero (v : ℕ→ℕ) (level cursor : ℕ)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,pathLoaded v level cursor j=0 := by
  intro j hj
  have bounds : j=220 ∨ j=221 ∨ j=222 ∨ j=223 := by
    simpa only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] using hj
  rw [pathLoaded_other v level cursor j (by omega) (by omega)]
  exact zero j hj

theorem emission_other {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) (j : ℕ) (outside : j∉({1226,1227,1228,1229,1230,1233,1234} : Finset ℕ)) :
    emissionValues p round saved i level cursor transpose j=advanced p round saved i j := by
  have o : j≠1226 ∧ j≠1227 ∧ j≠1228 ∧ j≠1229 ∧ j≠1230 ∧ j≠1233 ∧ j≠1234 := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using outside
  rw [emissionValues,origin_other transpose _ j (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or];tauto)]
  exact pathLoaded_other _ _ _ _ o.2.2.2.2.2.1 o.2.2.2.2.2.2

theorem emission_cursor {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) : emissionValues p round saved i level cursor transpose 1234=cursor := by
  rw [emissionValues,origin_other transpose _ 1234 (by decide)]
  rfl

theorem emission_choice {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) :
    rowChoice.evaluate (emissionValues p round saved i level cursor transpose)=
      moveShape (RowLayer.movement (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i)) :=
  (rowChoice_congr _ _ (emission_other p round saved i level cursor transpose 1211 (by decide))
    (emission_other p round saved i level cursor transpose 1212 (by decide))).trans (rowChoice_advanced p round saved i)

#print axioms emission_choice
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
