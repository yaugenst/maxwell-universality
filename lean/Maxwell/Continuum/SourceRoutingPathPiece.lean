import Maxwell.Continuum.SourceRoutingPathOrigin

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Maxwell.Logical.Routing GeometrySort GeometryArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def moveShape : RowLayer.Move→Shape
  | .idle => .idle
  | .exchange _ strand => .swap strand

def moveColumn {q : ℕ} (port : Port q) : RowLayer.Move→ℕ
  | .idle => port.1.val
  | .exchange lower _ => lower

theorem rowChoice_congr (v u : ℕ→ℕ) (direction : v 1211=u 1211) (exchange : v 1212=u 1212) :
    rowChoice.evaluate v=rowChoice.evaluate u := by
  simp only [rowChoice,ShapeChoice.evaluate,direction,exchange]

theorem rowChoice_decision {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    rowChoice.evaluate (decision p round saved i)=moveShape (RowLayer.movement
      (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i)) := by
  rw [←movement_eq]
  simp only [rowChoice,ShapeChoice.evaluate,decision_flag,decision_direction,movement]
  by_cases exchange : exchanges round saved (finProdFinEquiv.symm i)
  · by_cases direction : 0<maximumFlag round (finProdFinEquiv.symm i)
    · have nonzero : ¬maximumFlag round (finProdFinEquiv.symm i)=0 := by omega
      simp only [exchange,ite_true,show (0 : ℕ)<1 by decide,direction,nonzero,decide_false,moveShape]
    · have zero : maximumFlag round (finProdFinEquiv.symm i)=0 := by omega
      simp only [exchange,ite_true,show (0 : ℕ)<1 by decide,zero,Nat.lt_irrefl,ite_false,decide_true,moveShape]
  · simp only [exchange,ite_false,show ¬(0 : ℕ)<0 by decide,moveShape]

theorem rowChoice_advanced {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    rowChoice.evaluate (advanced p round saved i)=moveShape (RowLayer.movement
      (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i)) :=
  (rowChoice_congr _ _ (advanced_other p round saved i 1211 (by decide))
    (advanced_other p round saved i 1212 (by decide))).trans (rowChoice_decision p round saved i)

theorem originColumn_advanced {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    originColumn (advanced p round saved i)=moveColumn (finProdFinEquiv.symm i)
      (RowLayer.movement (SortArrays.arraySelection round saved) (finProdFinEquiv.symm i)) := by
  rw [originColumn,advanced_other p round saved i 1212 (by decide),decision_flag,
    advanced_lower,advanced_other p round saved i 1203 (by decide),decision_column,←movement_eq]
  by_cases exchange : exchanges round saved (finProdFinEquiv.symm i)
  · simp only [movement,exchange,ite_true,show (0 : ℕ)<1 by decide,moveColumn]
  · simp only [movement,exchange,ite_false,show ¬(0 : ℕ)<0 by decide,moveColumn]
    rfl

theorem moveShape_length {q parity : ℕ} (selected : RowLayer.Selection q parity) (port : Port q) :
    (moveShape (RowLayer.movement selected port)).length=RowLayer.pathLength selected port := by
  cases h : RowLayer.movement selected port <;> simp [moveShape,Shape.length,RowLayer.pathLength,h]

theorem moveShape_point {q parity : ℕ} (selected : RowLayer.Selection q parity) (port : Port q)
    (level : ℕ) (i : Fin (moveShape (RowLayer.movement selected port)).length) :
    translate (16*moveColumn port (RowLayer.movement selected port),16*port.2.val,16*level)
      ((moveShape (RowLayer.movement selected port)).point i)=
      translate (0,0,16*level) (RowLayer.pathPoint selected port i.val) := by
  revert i
  cases h : RowLayer.movement selected port with
  | idle => intro i;simp [moveColumn,moveShape,Shape.point,RowLayer.pathPoint,h,translate]
  | exchange lower strand =>
    intro i
    simp [moveColumn,moveShape,Shape.point,RowLayer.pathPoint,h,translate]

theorem decision_seed_other {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (i : Fin (q*q)) (j : ℕ) (hj : j∉GeometrySort.temporary) :
    decision p round saved i j=seed p round i.val j := by
  have hp : j∉partnerProgram.writes := fun h => hj
    (List.mem_toFinset.mp ((show partnerProgram.writes⊆GeometrySort.temporary.toFinset by decide) h))
  have h8 : j≠1208 := by intro h;subst j;exact hj (by decide)
  have h9 : j≠1209 := by intro h;subst j;exact hj (by decide)
  have hc : j∉({1212,1222,1223,1224} : Finset ℕ) := by
    intro h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl <;> exact hj (by decide)
  rw [decision_other p round saved i j hc]
  simp only [beforeSelect,afterSelf,Function.update_of_ne h8,Function.update_of_ne h9]
  exact intermediate_other p round i j hp

#print axioms moveShape_point
#print axioms rowChoice_advanced
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
