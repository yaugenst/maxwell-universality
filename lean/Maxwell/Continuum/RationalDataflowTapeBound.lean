import Maxwell.Continuum.RationalDataflowControl
import Maxwell.Cost.Structured.NatAssignTapeBound

/-! Symbolic bounds for the rational compiler. The bound depends on its
logical register bank, so generated determinant circuits remain opaque. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

theorem ids_bound (S : Finset ℕ) (N : ℕ) (bound : ∀i∈S,i<N) :
    ∀i∈ids S,i<1000+3*N := by
  intro i hi
  rcases Finset.mem_union.mp hi with bank | scratch
  · obtain ⟨j,hj,cell⟩:=Finset.mem_biUnion.mp bank
    have h:=bound j hj
    simp only [cellPorts,positivePort,negativePort,denominatorPort,
      Finset.mem_insert,Finset.mem_singleton] at cell
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at scratch
    omega

theorem workspace_bound (S : Finset ℕ) (N : ℕ) (bound : ∀i∈S,i<N) :
    ∀i∈workspace S,i<1000+3*N := by
  intro i hi
  rcases Finset.mem_union.mp hi with scratch | bank
  · simp only [Finset.mem_insert,Finset.mem_singleton] at scratch
    omega
  · exact ids_bound S N bound i bank

theorem rationalMagnitude_tapeBound : RationalMagnitude.program.tapeBound≤1000 := by decide +kernel

theorem stage_tapeBound (S : Finset ℕ) (N : ℕ) (bound : ∀i∈S,i<N)
    (stage : List NatAssign.Instruction) (valid : ∀a∈stage,a.Valid (ids S)) :
    (NatAssign.code stage).tapeBound≤1000+3*N :=
  NatAssign.code_tapeBound_le stage (ids S) _ valid (by omega) (ids_bound S N bound)

theorem inverseCode_tapeBound (S : Finset ℕ) (N : ℕ) (bound : ∀i∈S,i<N)
    (target source : ℕ) (ht : target∈S) (hs : source∈S) :
    (inverseCode target source).tapeBound≤1000+3*N := by
  exact max_le (stage_tapeBound S N bound _ (prepareInverse_valid S source hs))
    (max_le (rationalMagnitude_tapeBound.trans (by omega))
      (max_le (stage_tapeBound S N bound _ (inverseTail_valid S true target source ht hs))
        (stage_tapeBound S N bound _ (inverseTail_valid S false target source ht hs))))

theorem Instruction.tapeBound_le (instruction : Instruction) (S : Finset ℕ) (N : ℕ)
    (valid : instruction.Valid S) (bound : ∀i∈S,i<N) : instruction.code.tapeBound≤1000+3*N := by
  cases instruction with
  | literal target value => exact stage_tapeBound S N bound _ (literalStage_valid S target valid _)
  | binary op target left right =>
    exact stage_tapeBound S N bound _ (binaryStage_valid S op target left right valid.1 valid.2.1 valid.2.2)
  | inverse target source => exact inverseCode_tapeBound S N bound target source valid.1 valid.2

theorem program_tapeBound (instructions : List Instruction) (S : Finset ℕ) (N : ℕ)
    (valid : ∀instruction∈instructions,instruction.Valid S) (bound : ∀i∈S,i<N) :
    (program instructions).tapeBound≤1000+3*N := by
  induction instructions with
  | nil => exact Nat.zero_le _
  | cons instruction rest ih =>
    exact max_le (instruction.tapeBound_le S N (valid instruction (by simp)) bound)
      (ih (fun a ha => valid a (List.mem_cons_of_mem _ ha)))

theorem Control.tapeBound_le (control : Control) (S : Finset ℕ) (N : ℕ)
    (valid : control.Valid S) (bound : ∀i∈S,i<N) : control.code.tapeBound≤1000+3*N := by
  induction control with
  | done => exact Nat.zero_le _
  | step instruction rest ih => exact max_le (instruction.tapeBound_le S N valid.1 bound) (ih valid.2)
  | positive source yes no ih₁ ih₂ =>
    have prefixBound : (positivePrefix source).tapeBound≤1000+3*N :=
      max_le (stage_tapeBound S N bound _ (preparePositive_valid S source valid.1))
        (rationalMagnitude_tapeBound.trans (by omega))
    have cleanupBound :=stage_tapeBound S N bound _ (clearMagnitude_valid S)
    exact max_le prefixBound (max_le (max_le cleanupBound (ih₁ valid.2.1))
      (max_le cleanupBound (ih₂ valid.2.2)))

#print axioms Control.tapeBound_le
end Maxwell.Continuum.RationalDataflow
