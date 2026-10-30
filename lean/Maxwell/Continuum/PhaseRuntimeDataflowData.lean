import Maxwell.Continuum.PhaseRuntimeCost
import Maxwell.Continuum.PhaseDataflowFinish
import Maxwell.Continuum.NatAssignExternalWord

/-! Shared-register phase calls with preserved stored range and precision.
The finite code depends only on the output/input register addresses and a
four-element sign cycle. -/
namespace Maxwell.Continuum.RationalDataflow.Phase.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def privateTapes : List ℕ := Phase.privateTapes++[607,608,619,628,632,633,650,651,654,655,656,657]
def allIds (S : Finset ℕ) : Finset ℕ := RationalDataflow.ids S∪PhaseMachine.Runtime.ids
def workspace (S : Finset ℕ) : Finset ℕ := {0,1,2,3}∪allIds S
def Clean (s : BitRAMState) : Prop := ∀i∈(PhaseMachine.Runtime.ids.erase 652).erase 653,Blank s i
def parameters (Q N : ℕ) (v : ℕ→ℕ) : ℕ→ℕ := Function.update (Function.update v 652 Q) 653 N
def initialValues (Q N : ℕ) (v : ℕ→Parts) : ℕ→ℕ := parameters Q N (dataValues v)
def prepareCall (source : ℕ) : List NatAssign.Instruction :=
  [.copy 34 650,.copy (denominatorPort source) 651]++clearMagnitude
def seeded (Q N : ℕ) (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  NatAssign.values (prepareCall source) (parameters Q N (afterInverseMagnitude v source))
def returned (base : RationalTaylor.Runtime.Cycle) (Q N : ℕ) (v : ℕ→Parts) (source i : ℕ) : ℕ :=
  if i∈PhaseMachine.Runtime.ids then
    PhaseMachine.Runtime.finalValues (Phase.negative (v source)) base
      (Phase.magnitude (v source)) (v source).denominator Q N i else dataValues v i
def finishCall (target : ℕ) : List NatAssign.Instruction :=
  Phase.copyOutput target++NatAssign.clearList privateTapes
def code (base : RationalTaylor.Runtime.Cycle) (target source : ℕ) : Code :=
  .seq (NatAssign.code (prepareInverse source))
    (.seq RationalMagnitude.program (.seq (.atom (.bitAnd 200 23 23))
      (.seq (NatAssign.code (prepareCall source))
        (.seq (PhaseMachine.Runtime.program base) (NatAssign.code (finishCall target))))))

theorem ids_small (i : ℕ) (hi : i∈PhaseMachine.Runtime.ids) : i<1000 := by
  rcases Finset.mem_union.mp hi with hi|hi
  · exact PhaseMachine.allIds_small i hi
  · simp only [PhaseMachine.Runtime.extras,Finset.mem_insert,Finset.mem_singleton] at hi
    omega

theorem privateTapes_mem (i : ℕ) :
    i∈privateTapes ↔ i∈PhaseMachine.Runtime.ids ∧ i≠652 ∧ i≠653 := by
  simp only [privateTapes,List.mem_append,Phase.privateTapes_mem,PhaseMachine.Runtime.ids,
    PhaseMachine.Runtime.extras,PhaseMachine.allIds,PhaseMachine.ids,Machin.allIds,RationalArctan.ids,
    RationalTaylor.ids,RationalMagnitude.ids,List.mem_cons,List.not_mem_nil,or_false,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem parameter_outside (S : Finset ℕ) (i : ℕ) (hi : i=652 ∨ i=653) : i∉RationalDataflow.ids S := by
  intro hm
  rcases Finset.mem_union.mp hm with hm|hm
  · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hm
    have hp := positivePort_ge r
    have hn := negativePort_ge r
    have hd := denominatorPort_ge r
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hm
    omega

theorem prepare_values (Q N : ℕ) (v : ℕ→Parts) (source : ℕ) :
    NatAssign.values (prepareInverse source) (initialValues Q N v)=parameters Q N (beforeInverse v source) := by
  rw [initialValues,parameters,NatAssign.values_update_outside (RationalDataflow.ids {source}) _
    (prepareInverse_valid {source} source (by simp)) _ 653 N (parameter_outside _ _ (by omega)),
    NatAssign.values_update_outside (RationalDataflow.ids {source}) _
    (prepareInverse_valid {source} source (by simp)) _ 652 Q (parameter_outside _ _ (by omega)),
    prepareInverse_values]
  rfl

theorem seeded_small (Q N : ℕ) (v : ℕ→Parts) (source i : ℕ) (hi : i<1000) :
    seeded Q N v source i=PhaseMachine.Runtime.initialValues
      (Phase.magnitude (v source)) (v source).denominator Q N i := by
  have hs := denominatorPort_ge source
  simp (disch := omega) [seeded,prepareCall,clearMagnitude,afterInverseMagnitude,beforeInverse,parameters,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    Function.update_apply,dataValues_small v hi,PhaseMachine.Runtime.initialValues,Phase.magnitude]
  split_ifs <;> omega

theorem seeded_large (Q N : ℕ) (v : ℕ→Parts) (source i : ℕ) (hi : 1000 ≤ i) :
    seeded Q N v source i=dataValues v i := by
  apply (values_unchanged (prepareCall source) _ i (by
    simp only [prepareCall,clearMagnitude,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with (h|h)|(h|h|h|h|h|h|h) <;>
      subst a <;> simp only [NatAssign.Instruction.target] <;> omega)).trans
  simp only [parameters,afterInverseMagnitude,beforeInverse,
    Function.update_of_ne (by omega : i≠653),Function.update_of_ne (by omega : i≠652),
    Function.update_of_ne (by omega : i≠34),Function.update_of_ne (by omega : i≠31),
    Function.update_of_ne (by omega : i≠30)]

theorem seeded_outside (Q N : ℕ) (v : ℕ→Parts) (source i : ℕ) (hi : i∉PhaseMachine.Runtime.ids) :
    seeded Q N v source i=dataValues v i := by
  by_cases hs : i<1000
  · rw [seeded_small Q N v source i hs,dataValues_small v hs]
    have h650 : i≠650 := by intro h;subst i;exact hi (by decide)
    have h651 : i≠651 := by intro h;subst i;exact hi (by decide)
    have h652 : i≠652 := by intro h;subst i;exact hi (by decide)
    have h653 : i≠653 := by intro h;subst i;exact hi (by decide)
    simp only [PhaseMachine.Runtime.initialValues,h650,h651,h652,h653,ite_false]
  · exact seeded_large Q N v source i (by omega)

theorem returned_output (base : RationalTaylor.Runtime.Cycle) (Q N : ℕ) (v : ℕ→Parts) (source : ℕ) :
    (⟨returned base Q N v source 602,returned base Q N v source 603,
      returned base Q N v source 604⟩ : Parts)=Phase.result (RationalTaylor.Runtime.cycleSigns base) Q N (v source) := by
  simp only [returned,Phase.result,show 602∈PhaseMachine.Runtime.ids by decide,
    show 603∈PhaseMachine.Runtime.ids by decide,show 604∈PhaseMachine.Runtime.ids by decide,ite_true,
    PhaseMachine.Runtime.finalValues_core _ _ _ _ _ _ 602 (by decide),
    PhaseMachine.Runtime.finalValues_core _ _ _ _ _ _ 603 (by decide),
    PhaseMachine.Runtime.finalValues_core _ _ _ _ _ _ 604 (by decide)]

theorem returned_parameters (base : RationalTaylor.Runtime.Cycle) (Q N : ℕ) (v : ℕ→Parts) (source : ℕ) :
    returned base Q N v source 652=Q ∧ returned base Q N v source 653=N := by
  simp only [returned,show 652∈PhaseMachine.Runtime.ids by decide,show 653∈PhaseMachine.Runtime.ids by decide,ite_true]
  rw [PhaseMachine.Runtime.finalValues_extra _ _ _ _ _ _ 652 (by decide),
    PhaseMachine.Runtime.finalValues_extra _ _ _ _ _ _ 653 (by decide)]
  simp [PhaseMachine.Runtime.initialValues]

#print axioms seeded_small
#print axioms returned_output
end Maxwell.Continuum.RationalDataflow.Phase.Runtime
