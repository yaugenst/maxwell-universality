import Maxwell.Logical.Routing.SortPaths
import Maxwell.Logical.Routing.PhaseKeys

/-! Endpoint identities for row-column-row traversal of stored histories.
These depend only on routing permutations and can be used by either realization. -/
namespace Maxwell.Logical.Routing.SortPaths
open SortSchedule

def nextStart {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) : Port q :=
  (port initial start (2*q)).swap

theorem threePhase_target {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (start : Port q) :
    port (PhaseKeys.last colors)
      (nextStart (PhaseKeys.middle colors) (nextStart (PhaseKeys.first colors) start)) (2*q)=target start := by
  have firstRow : ∀p,((PhaseArrays.prepare colors).first p).2=p.2 := by
    rw [PhaseArrays.prepare_first]
    exact first_phase_preserves_row colors
  have middleRow : ∀p,(transposedTarget (PhaseArrays.prepare colors).column p).2=p.2 := by
    intro p
    change ((PhaseArrays.prepare colors).column p.swap).1=p.2
    rw [PhaseArrays.prepare_column]
    exact column_phase_preserves_column colors p.swap
  have lastRow : ∀p,((PhaseArrays.prepare colors).finalRow p).2=p.2 := by
    rw [PhaseArrays.prepare_finalRow]
    exact final_phase_preserves_row colors
  simp only [PhaseKeys.first,PhaseKeys.middle,PhaseKeys.last,nextStart,port_target _ firstRow,
    port_target _ middleRow,port_target _ lastRow]
  change (PhaseArrays.prepare colors).finalRow
    ((PhaseArrays.prepare colors).column ((PhaseArrays.prepare colors).first start))=target start
  exact PhaseArrays.prepare_routes colors start

/-- A reverse history traversal consumes the same comparisons in descending order. -/
def reversePort {q : ℕ} (initial : SortArrays.Keys q) : ℕ→Port q→Port q
  | 0, finish => finish
  | k+1, finish => reversePort initial k
      (RowLayer.destination (SortArrays.arraySelection (k+1) (SortArrays.run initial k)) finish)

theorem reversePort_forward {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (k : ℕ) :
    reversePort initial k (port initial start k)=start := by
  induction k with
  | zero => rfl
  | succ k ih => rw [reversePort,port_reverse_step,ih]

theorem forward_reversePort {q : ℕ} (initial : SortArrays.Keys q) (finish : Port q) (k : ℕ) :
    port initial (reversePort initial k finish) k=finish := by
  induction k generalizing finish with
  | zero => rfl
  | succ k ih =>
    rw [reversePort,port,ih]
    exact RowLayer.destination_involutive _ _

#print axioms threePhase_target
#print axioms reversePort_forward
#print axioms forward_reversePort
end Maxwell.Logical.Routing.SortPaths
