import Maxwell.Continuum.SourceRoutingGeometryControlValues

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured

def Control.writes : Control→Finset ℕ
  | .done => ∅
  | .assign a rest => {a.target}∪rest.writes
  | .divide _ _ q r rest => {q,r}∪rest.writes
  | .decrement target rest => {target}∪rest.writes
  | .positive _ yes no => yes.writes∪no.writes

theorem Control.evaluate_other (c : Control) (v : ℕ→ℕ) (j : ℕ) (hj : j∉c.writes) : c.evaluate v j=v j := by
  induction c generalizing v with
  | done => rfl
  | assign a rest ih =>
    simp only [Control.writes,Finset.mem_union,Finset.mem_singleton,not_or] at hj
    exact (ih (a.update v) hj.2).trans (Function.update_of_ne hj.1 _ _)
  | divide source divisor quotient remainder rest ih =>
    simp only [Control.writes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    exact (ih _ hj.2).trans (divided_other v source divisor quotient remainder j hj.1.1 hj.1.2)
  | decrement target rest ih =>
    simp only [Control.writes,Finset.mem_union,Finset.mem_singleton,not_or] at hj
    exact (ih _ hj.2).trans (Function.update_of_ne hj.1 _ _)
  | positive source yes no iy ino =>
    simp only [Control.writes,Finset.mem_union,not_or] at hj
    by_cases hp : 0<v source
    · rw [Control.positive_true _ _ _ _ hp];exact iy v hj.1
    · rw [Control.positive_false _ _ _ _ hp];exact ino v hj.2

#print axioms Control.evaluate_other
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
