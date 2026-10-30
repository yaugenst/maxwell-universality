import Maxwell.Continuum.SourceRoutingPathNextState

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem emission_level {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) : emissionValues p round saved i level cursor transpose 1233=level := by
  rw [emissionValues,origin_other transpose _ 1233 (by decide)]
  rfl

theorem emission_zero {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      emissionValues p round saved i level cursor transpose j=0 :=
  (originProgram transpose).evaluate_zero (origin_valid transpose) _
    (pathLoaded_zero _ level cursor (advanced_zero p round saved i))

theorem emission_seed_field {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor : ℕ) (transpose : Bool) (j : ℕ) (hj : j∈({1200,1202,1215,1216,1217,1219,1220} : Finset ℕ)) :
    emissionValues p round saved i level cursor transpose j=GeometrySort.seed p round i.val j := by
  have outside : j∉({1226,1227,1228,1229,1230,1233,1234} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    omega
  rw [emission_other p round saved i level cursor transpose j outside]
  apply advanced_seed_other
  all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  · simp only [GeometrySort.temporary,List.mem_cons,List.not_mem_nil,or_false]
    omega
  all_goals omega

theorem nextFields_emission {q : ℕ} (p : GeometryHistory.Plan q) (k : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q))
    (level cursor nextCursor : ℕ) (transpose : Bool) :
    NextFields p k
      (finProdFinEquiv (RowLayer.destination (SortArrays.arraySelection (k+1) saved) (finProdFinEquiv.symm i))).val
      (cursorValues (emissionValues (p.layer k) (k+1) saved i level cursor transpose) nextCursor) := by
  have core (j : ℕ) (hj : j∈({1200,1202,1215,1216,1217,1219,1220} : Finset ℕ)) :
      cursorValues (emissionValues (p.layer k) (k+1) saved i level cursor transpose) nextCursor j=
        GeometrySort.seed (p.layer k) (k+1) i.val j := by
    rw [cursorValues_other _ _ j (by simp only [Finset.mem_insert,Finset.mem_singleton] at hj;omega)]
    exact emission_seed_field _ _ _ _ _ _ _ _ hj
  refine ⟨core 1200 (by decide),core 1202 (by decide),core 1215 (by decide),core 1216 (by decide),
    core 1217 (by decide),core 1219 (by decide),core 1220 (by decide),?_,?_⟩
  · rw [cursorValues_other _ _ 1214 (by decide),emission_other _ _ _ _ _ _ _ 1214 (by decide),advanced_destination]
  · intro j hj
    have small : j<1200 := by
      simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
        Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    rw [cursorValues_other _ _ j (by omega)]
    exact emission_zero _ _ _ _ _ _ _ j hj

theorem NextFields.level_update {q : ℕ} {p : GeometryHistory.Plan q} {k next : ℕ} {v : ℕ→ℕ}
    (fields : NextFields p k next v) (level : ℕ) : NextFields p k next (Function.update v 1233 level) := by
  refine ⟨fields.count,fields.round,fields.source,fields.destination,fields.width,fields.one,fields.two,fields.nextPort,?_⟩
  intro j hj
  have small : j<1200 := by
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  rw [Function.update_of_ne (by omega : j≠1233)]
  exact fields.quotient j hj

#print axioms nextFields_emission
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
