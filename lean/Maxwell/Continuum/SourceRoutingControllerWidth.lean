import Maxwell.Continuum.SourceRoutingLevelWidths
import Maxwell.Continuum.SourceRoutingLevelAdvanceValues

/-! Old temporary words never feed the next node descriptor.  This
dependency fact gives one width bound for every level of the whole tree. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ControllerWidth
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def reads : Finset ℕ := {806,809,811,812,813,814,815,819}
def restricted (v : ℕ→ℕ) (i : ℕ) : ℕ := if i∈reads then v i else 0

theorem output_dependency (v : ℕ→ℕ) (i : ℕ) (hi : i∈Level.writes) :
    Step.output v i=Step.output (restricted v) i := by
  simp only [Level.writes,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [Step.output,Step.increment,Descriptor.output,Descriptor.divided,
    Descriptor.prepare,Descriptor.finish,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update,restricted,reads]

theorem restricted_width (v : ℕ→ℕ) (L : ℕ)
    (hv : ∀i∈reads,(v i).bits.length ≤ L) :
    ∀i∈Division.ids,(restricted v i).bits.length ≤ L := by
  intro i _
  by_cases hi : i∈reads
  · simpa [restricted,hi] using hv i hi
  · simp [restricted,hi]

theorem basis_width (v : ℕ→ℕ) (n L : ℕ)
    (hv : ∀i∈reads,(v i).bits.length ≤ L) (hn : n.bits.length ≤ L) :
    ∀i∈reads,(Level.basis v n i).bits.length ≤ 2*L+1 := by
  intro i hi
  by_cases he : i=815
  · subst i
    have h0:=hv 815 (by decide)
    have h1:=RationalAccumulator.bits_add_le (v 815) n
    change (v 815+n).bits.length ≤ 2*L+1
    omega
  · simpa only [Level.basis,Function.update_of_ne he] using (hv i hi).trans (by omega : L ≤ 2*L+1)

theorem values_width (v : ℕ→ℕ) (n L T : ℕ) (hL : 1 ≤ L)
    (hv : ∀i∈reads,(v i).bits.length ≤ L)
    (ht : ∀i∈Division.ids,(v i).bits.length ≤ T)
    (hn : n.bits.length ≤ L) (hT : Level.uniformWidth L ≤ T) :
    ∀i∈Division.ids,(Level.values v n i).bits.length ≤ T := by
  cases n with
  | zero => exact ht
  | succ n =>
      rw [Level.values_successor]
      intro i hi
      by_cases written : i∈Level.writes
      · rw [output_dependency _ _ written]
        have bw:=restricted_width (Level.basis v n) (2*L+1)
          (basis_width v n L hv ((Maxwell.Continuum.RationalWords.bits_mono (Nat.le_succ n)).trans hn))
        have hh:=Level.output_width (restricted (Level.basis v n)) (2*L+1) (by omega) bw i hi
        exact hh.trans ((by dsimp only [Level.uniformWidth,Step.wordBound];omega :
          4*(Step.wordBound (2*L+1)+1) ≤ Level.uniformWidth L).trans hT)
      · rw [Level.output_other _ _ written]
        have h815 : i≠815 := by intro he;subst i;exact written (by decide)
        simpa only [Level.basis,Function.update_of_ne h815] using ht i hi

theorem advance_dependency (v : ℕ→ℕ) (i : ℕ) (hi : i∈Level.Advance.writes) :
    Level.Advance.output v i=Level.Advance.output (restricted v) i := by
  simp only [Level.Advance.writes,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [Level.Advance.output,Level.Advance.instructions,Level.Advance.decreased,
    Level.Advance.divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update,restricted,reads]

theorem advance_width (v : ℕ→ℕ) (L T : ℕ)
    (hv : ∀i∈reads,(v i).bits.length ≤ L) (ht : ∀i∈Division.ids,(v i).bits.length ≤ T)
    (hT : Level.uniformWidth L ≤ T) :
    ∀i∈Division.ids,(Level.Advance.output v i).bits.length ≤ T := by
  have valid : ∀a∈Level.Advance.instructions,a.Valid Division.ids := by
    simp [Level.Advance.instructions,NatAssign.Instruction.Valid,Division.ids,Division.controls]
  have lit : ∀a∈Level.Advance.instructions,a.literalWidth ≤ L := by
    simp [Level.Advance.instructions,NatAssign.Instruction.literalWidth]
  intro i hi
  by_cases written : i∈Level.Advance.writes
  · rw [advance_dependency _ _ written]
    have hh:=NatAssign.values_width_bound Division.ids Level.Advance.instructions valid
      (Level.Advance.decreased (restricted v)) L
      (Level.Advance.decreased_width _ L (restricted_width v L hv)) lit i hi
    change (Level.Advance.output (restricted v) i).bits.length+1 ≤ 16*(L+1) at hh
    have small : 16*(L+1) ≤ Level.uniformWidth L := by dsimp only [Level.uniformWidth];omega
    omega
  · rw [Level.Advance.output_other v i written]
    exact ht i hi

#print axioms output_dependency
#print axioms values_width
#print axioms advance_width
end Maxwell.Cost.RoutingPorts.Complete.Tree.ControllerWidth
