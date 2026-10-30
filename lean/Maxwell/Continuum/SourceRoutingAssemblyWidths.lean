import Maxwell.Continuum.SourceRoutingAssemblyValues
import Maxwell.Continuum.SourceRoutingControllerWidth

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def uniformWidth (L : ℕ) : ℕ := 2^40*(L+2)

theorem output_width (v : ℕ→ℕ) (B : ℕ) (hB : 4 ≤ B)
    (hw : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(AssemblyStep.output v i).bits.length ≤ 4*(AssemblyDescriptor.wordBound B+1) := by
  have valid : ∀a∈Step.increment,a.Valid Division.ids := by
    simp [Step.increment,NatAssign.Instruction.Valid,Division.ids,Division.controls]
  have lit : ∀a∈Step.increment,a.literalWidth ≤ AssemblyDescriptor.wordBound B := by
    simp [Step.increment,NatAssign.Instruction.literalWidth,AssemblyDescriptor.wordBound]
    exact Nat.succ_le_of_lt (by positivity)
  intro i hi
  have hh:=NatAssign.values_width_bound Division.ids Step.increment valid (AssemblyDescriptor.output v)
    (AssemblyDescriptor.wordBound B) (AssemblyDescriptor.output_word_width v B hB hw) lit i hi
  exact (Nat.le_add_right _ 1).trans hh

theorem output_dependency (v : ℕ→ℕ) (i : ℕ) (hi : i∈writes) :
    AssemblyStep.output v i=AssemblyStep.output (ControllerWidth.restricted v) i := by
  simp only [writes,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [AssemblyStep.output,Step.increment,AssemblyDescriptor.output,AssemblyDescriptor.divided,
    AssemblyDescriptor.finish,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,Function.update,ControllerWidth.restricted,ControllerWidth.reads]

theorem values_width (v : ℕ→ℕ) (n L T : ℕ) (hL : 2 ≤ L)
    (hv : ∀i∈ControllerWidth.reads,(v i).bits.length ≤ L)
    (ht : ∀i∈Division.ids,(v i).bits.length ≤ T)
    (hn : n.bits.length ≤ L) (hT : uniformWidth L ≤ T) :
    ∀i∈Division.ids,(values v n i).bits.length ≤ T := by
  cases n with
  | zero => exact ht
  | succ n =>
      rw [values_successor]
      intro i hi
      by_cases written : i∈writes
      · rw [output_dependency _ _ written]
        have bw:=ControllerWidth.restricted_width (Level.basis v n) (2*L+1)
          (ControllerWidth.basis_width v n L hv
            ((Maxwell.Continuum.RationalWords.bits_mono (Nat.le_succ n)).trans hn))
        have hh:=output_width (ControllerWidth.restricted (Level.basis v n)) (2*L+1) (by omega) bw i hi
        exact hh.trans ((by dsimp only [uniformWidth,AssemblyDescriptor.wordBound];omega :
          4*(AssemblyDescriptor.wordBound (2*L+1)+1) ≤ uniformWidth L).trans hT)
      · rw [output_other _ _ written]
        have h815 : i≠815 := by intro he;subst i;exact written (by decide)
        simpa only [Level.basis,Function.update_of_ne h815] using ht i hi

theorem values_simple_width (v : ℕ→ℕ) (n L : ℕ) (hL : 2 ≤ L)
    (hv : ∀i∈Division.ids,(v i).bits.length ≤ L) (hn : n.bits.length ≤ L) :
    ∀i∈Division.ids,(values v n i).bits.length ≤ uniformWidth L := by
  have subset : ControllerWidth.reads⊆Division.ids := by decide
  have larger : L ≤ uniformWidth L := (Nat.le_add_right L 2).trans
    (Nat.le_mul_of_pos_left (L+2) (by decide : 0<2^40))
  exact values_width v n L (uniformWidth L) hL (fun i hi => hv i (subset hi))
    (fun i hi => (hv i hi).trans larger) hn le_rfl

#print axioms values_width
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
