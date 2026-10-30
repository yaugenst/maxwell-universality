import Maxwell.Continuum.GlueRuntimeCost
import Maxwell.Continuum.PhaseDataflowData
import Maxwell.Cost.WordCall

/-! Shared-register glue calls retain the runtime precision and clear every
private arithmetic word, including the padded Taylor countdown. -/
namespace Maxwell.Continuum.RationalDataflow.Glue
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

abbrev Core := GlueMachine.Runtime.core

def privateTapes : List ℕ :=
  [30,31,32,33,34,35,36,600,601,602,603,604,605,606,607,608,609,642,643]
def allIds (S : Finset ℕ) : Finset ℕ := RationalDataflow.ids S∪GlueMachine.Runtime.ids
def workspace (S : Finset ℕ) : Finset ℕ := {0,1,2,3}∪allIds S
def Clean (s : BitRAMState) : Prop :=
  ∀i∈GlueMachine.Runtime.ids.erase 640,Blank s i

def initialValues (N : ℕ) (v : ℕ→Parts) : ℕ→ℕ := Function.update (dataValues v) 640 N

def result (N : ℕ) (x : Parts) : Parts :=
  if x.positive<x.negative then Parts.literal 0
  else GlueMachine.Runtime.result (Phase.magnitude x) x.denominator N

def prepareCall (source : ℕ) : List NatAssign.Instruction :=
  [.copy 34 600,.copy (denominatorPort source) 601]++clearMagnitude

def seeded (N : ℕ) (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  NatAssign.values (prepareCall source) (Function.update (afterInverseMagnitude v source) 640 N)

def returned (N : ℕ) (v : ℕ→Parts) (source i : ℕ) : ℕ :=
  if i∈GlueMachine.Runtime.ids then
    GlueMachine.Runtime.finalValues (Phase.magnitude (v source)) (v source).denominator N i
  else dataValues v i

def unsignedFinished (N : ℕ) (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  Function.update (returned N v source) 641 0

def corrected (N : ℕ) (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  if (v source).positive<(v source).negative then
    NatAssign.values GlueMachine.writeZero (unsignedFinished N v source)
  else unsignedFinished N v source

def copyOutput (target : ℕ) : List NatAssign.Instruction :=
  [.copy 602 (positivePort target),.copy 603 (negativePort target),.copy 604 (denominatorPort target)]
def finishCall (target : ℕ) : List NatAssign.Instruction :=
  copyOutput target++NatAssign.clearList privateTapes

def code (target source : ℕ) : Code :=
  .seq (NatAssign.code (prepareInverse source))
    (.seq RationalMagnitude.program
      (.seq (.atom (.bitAnd 200 23 23))
        (.seq (NatAssign.code (prepareCall source))
          (.seq Core
            (.seq (.call (TapeOps.clear 641))
              (.seq (.branch 200 (NatAssign.code GlueMachine.writeZero) .skip)
                (NatAssign.code (finishCall target))))))))

theorem ids_small (i : ℕ) (hi : i∈GlueMachine.Runtime.ids) : i<1000 := by
  simp only [GlueMachine.Runtime.ids,GlueMachine.ids,GlueMachine.extra,
    SelectedParameters.Compare.ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton] at hi
  omega

theorem privateTapes_mem (i : ℕ) :
    i∈privateTapes ↔ i∈GlueMachine.Runtime.ids ∧ i≠640 ∧ i≠641 := by
  simp only [privateTapes,GlueMachine.Runtime.ids,GlueMachine.ids,GlueMachine.extra,
    SelectedParameters.Compare.ids,RationalTaylor.ids,List.mem_cons,List.not_mem_nil,
    or_false,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem result_value (N : ℕ) (x : Parts) (hx : x.Valid) :
    (result N x).value=(Profile.glueApprox x.value N).center := by
  by_cases hn : x.positive<x.negative
  · have hs : x.value≤0 := by
      unfold Parts.value
      apply div_nonpos_of_nonpos_of_nonneg
      · exact sub_nonpos.mpr (by exact_mod_cast hn.le)
      · positivity
    have hthreshold : x.value≤1/((N:ℚ)+1) := hs.trans (by positivity)
    simp only [result,ite_eq_left hn,Profile.glueApprox,ite_eq_left hthreshold,Parts.literal_value]
  · have he : (Phase.magnitude x:ℚ)/x.denominator=x.value := by
      simpa only [Phase.negative,decide_eq_false hn,RationalTaylor.signedFraction,
        Bool.false_eq_true,ite_false] using Phase.signedFraction_eq x
    rw [result,ite_eq_right hn,GlueMachine.Runtime.result_value _ _ _ hx,he]

theorem result_valid (N : ℕ) (x : Parts) (hx : x.Valid) : (result N x).Valid := by
  unfold result
  split_ifs
  · exact Parts.literal_valid 0
  · exact GlueMachine.Runtime.result_valid _ _ _ hx

theorem seeded_small (N : ℕ) (v : ℕ→Parts) (source i : ℕ) (hi : i<1000) :
    seeded N v source i=GlueMachine.Runtime.initialValues
      (Phase.magnitude (v source)) (v source).denominator N i := by
  have hs := denominatorPort_ge source
  simp (disch := omega) [seeded,prepareCall,clearMagnitude,afterInverseMagnitude,beforeInverse,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    Function.update_apply,dataValues_small v hi,GlueMachine.Runtime.initialValues,
    GlueMachine.initialValues,Phase.magnitude]
  split_ifs <;> omega

theorem seeded_large (N : ℕ) (v : ℕ→Parts) (source i : ℕ) (hi : 1000 ≤ i) :
    seeded N v source i=dataValues v i := by
  apply (values_unchanged (prepareCall source) _ i (by
    simp only [prepareCall,clearMagnitude,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with (h|h)|(h|h|h|h|h|h|h) <;>
      subst a <;> simp only [NatAssign.Instruction.target] <;> omega)).trans
  simp only [afterInverseMagnitude,beforeInverse,Function.update_of_ne (by omega : i≠640),
    Function.update_of_ne (by omega : i≠34),Function.update_of_ne (by omega : i≠31),
    Function.update_of_ne (by omega : i≠30)]

#print axioms result_value
#print axioms seeded_small
end Maxwell.Continuum.RationalDataflow.Glue
