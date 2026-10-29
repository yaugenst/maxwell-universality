import Maxwell.Cost.RealSimulation.VisitedSteps
import Maxwell.Cost.RealLink

namespace Maxwell.Cost.RealSimulation
open IndexWidth

/-- Linking preserves every natural data word, throughout the actual trace. -/
theorem VisitedSteps.relocate {outer body : Machine} {base returnPC : ℕ}
    {input : RAMInput} {tape : ℕ → Bool} {B cost : ℕ} {s t : RAMState}
    (trace : VisitedSteps (body.next input tape) (IndexBound B) cost s t)
    (placement : outer.Contains body base returnPC) :
    VisitedSteps (outer.next input tape) (IndexBound B) cost
      (s.relocate base) (t.relocate base) := by
  induction trace with
  | refl bound => exact .refl bound
  | step bound transition _ ih => exact .step bound (placement.next input tape transition) ih

/-- The compiled call's return jump is also included in the bounded trace. -/
theorem VisitedSteps.call {outer body : Machine} {base returnPC : ℕ}
    {input : RAMInput} {tape : ℕ → Bool} {B cost : ℕ} {s t : RAMState}
    (trace : VisitedSteps (body.next input tape) (IndexBound B) cost s t)
    (placement : outer.Contains body base returnPC) (halt : body.code[t.pc]?=some .halt) :
    VisitedSteps (outer.next input tape) (IndexBound B) (cost+1)
      (s.relocate base) {t with pc:=returnPC} := by
  have ht : IndexBound B t := trace.prefix le_rfl trace.steps
  have hr : IndexBound B (t.relocate base) := ht
  have he : IndexBound B {t with pc:=returnPC} := ht
  exact (trace.relocate placement).trans
    (.step hr (placement.return_step input tape t halt) (.refl he))

end Maxwell.Cost.RealSimulation
