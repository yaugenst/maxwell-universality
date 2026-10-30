import Maxwell.Continuum.PhaseMachineFinalBank
import Maxwell.Continuum.NatAssignCleanup
import Maxwell.Continuum.RationalDataflowInverse

/-! Literal shared-register phase calls. The input is an arbitrary
unreduced signed rational in Parts format; outputs are exact Taylor
center Parts, and all private work words are cleared before return. -/
namespace Maxwell.Continuum.RationalDataflow.Phase
open Maxwell.Cost Maxwell.Cost.Structured RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def privateTapes : List ℕ :=
  [30,31,32,33,34,35,36,600,601,602,603,604,605,606,
    610,611,612,613,614,615,616,617,618,620,621,622,623,624,625,626,627,630,631]

theorem privateTapes_mem (i : ℕ) : i∈privateTapes ↔ i∈PhaseMachine.allIds := by
  simp only [privateTapes,PhaseMachine.allIds,PhaseMachine.ids,Machin.allIds,
    RationalArctan.ids,RationalTaylor.ids,RationalMagnitude.ids,List.mem_cons,List.not_mem_nil,
    or_false,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  tauto

def allIds (S : Finset ℕ) : Finset ℕ := RationalDataflow.ids S∪PhaseMachine.allIds
def workspace (S : Finset ℕ) : Finset ℕ := {0,1,2,3}∪allIds S
def Clean (s : BitRAMState) : Prop := ∀i∈PhaseMachine.allIds,RationalAccumulator.Blank s i
def negative (x : Parts) : Bool := decide (x.positive<x.negative)
def magnitude (x : Parts) : ℕ := IntegerNormSquare.magnitude x.positive x.negative

def result (base : ℕ→Sign) (Q N : ℕ) (x : Parts) : Parts :=
  ⟨PhaseMachine.fullFinal (negative x) base (magnitude x) x.denominator Q N 602,
   PhaseMachine.fullFinal (negative x) base (magnitude x) x.denominator Q N 603,
   PhaseMachine.fullFinal (negative x) base (magnitude x) x.denominator Q N 604⟩

def prepareCall (source : ℕ) : List NatAssign.Instruction :=
  [.copy 34 630,.copy (denominatorPort source) 631]++clearMagnitude

def seeded (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  NatAssign.values (prepareCall source) (afterInverseMagnitude v source)

def returned (base : ℕ→Sign) (Q N : ℕ) (v : ℕ→Parts) (source i : ℕ) : ℕ :=
  if i∈PhaseMachine.allIds then
    PhaseMachine.fullFinal (negative (v source)) base (magnitude (v source)) (v source).denominator Q N i
  else dataValues v i

def copyOutput (target : ℕ) : List NatAssign.Instruction :=
  [.copy 602 (positivePort target),.copy 603 (negativePort target),.copy 604 (denominatorPort target)]
def finishCall (target : ℕ) : List NatAssign.Instruction :=
  copyOutput target++NatAssign.clearList privateTapes

def code (base : ℕ→Sign) (Q N target source : ℕ) : Code :=
  .seq (NatAssign.code (prepareInverse source))
    (.seq RationalMagnitude.program
      (.seq (.atom (.bitAnd 200 23 23))
        (.seq (NatAssign.code (prepareCall source))
          (.seq (PhaseMachine.program base Q N) (NatAssign.code (finishCall target))))))

theorem signedFraction_eq (x : Parts) : signedFraction (negative x) (magnitude x) x.denominator=x.value := by
  by_cases h : x.positive<x.negative
  · simp only [negative,h,decide_true,signedFraction,ite_true,magnitude,Parts.magnitude_eq_of_lt x h]
    rw [Nat.cast_sub h.le]
    unfold Parts.value
    ring
  · simp only [negative,h,decide_false,signedFraction,Bool.false_eq_true,ite_false,magnitude,
      Parts.magnitude_eq_of_le x (by omega)]
    rw [Nat.cast_sub (by omega : x.negative≤x.positive)]
    rfl

theorem result_value (base : ℕ→Sign) (Q N : ℕ) (x : Parts) :
    (result base Q N x).value=
      RationalTaylor.value (PhaseMachine.argumentNumerator (magnitude x) Q N)
        (PhaseMachine.argumentDenominator x.denominator Q N)
        (fractionSigns (negative x) base) (PhaseMachine.order Q N) := by
  simp only [result,Parts.value,PhaseMachine.fullFinal,RationalTaylor.extendedValues,
    show 602∈RationalTaylor.ids by decide,show 603∈RationalTaylor.ids by decide,
    show 604∈RationalTaylor.ids by decide,
    (PhaseMachine.fullPrepared_inputs (magnitude x) x.denominator Q N).1,
    (PhaseMachine.fullPrepared_inputs (magnitude x) x.denominator Q N).2,
    RationalTaylor.values,RationalTaylor.value]
  norm_num

theorem result_valid (base : ℕ→Sign) (Q N : ℕ) (x : Parts) (hx : x.Valid) :
    (result base Q N x).Valid := by
  change 0<PhaseMachine.fullFinal (negative x) base (magnitude x) x.denominator Q N 604
  simp only [PhaseMachine.fullFinal,RationalTaylor.extendedValues,
    show 604∈RationalTaylor.ids by decide,
    (PhaseMachine.fullPrepared_inputs (magnitude x) x.denominator Q N).1,
    (PhaseMachine.fullPrepared_inputs (magnitude x) x.denominator Q N).2,
    RationalTaylor.values]
  norm_num only [show ¬(604:ℕ)=600 by decide,show ¬(604:ℕ)=601 by decide,
    show ¬(604:ℕ)=602 by decide,show ¬(604:ℕ)=603 by decide,ite_false]
  exact RationalTaylor.denominator_pos (PhaseMachine.argumentDenominator_pos hx Q N) _

theorem result_cos (Q N : ℕ) (x : Parts) (hx : x.Valid) :
    (result cosineSigns Q N x).value=(Calibration.cosTurnApprox x.value Q N).center := by
  rw [result_value,←PhaseMachine.cosTurnApprox_center _ _ _ _ _ hx,signedFraction_eq]

theorem result_sin (Q N : ℕ) (x : Parts) (hx : x.Valid) :
    (result sineSigns Q N x).value=(Calibration.sinTurnApprox x.value Q N).center := by
  rw [result_value,←PhaseMachine.sinTurnApprox_center _ _ _ _ _ hx,signedFraction_eq]

theorem seeded_small (v : ℕ→Parts) (source i : ℕ) (hi : i<1000) :
    seeded v source i=PhaseMachine.initialValues (magnitude (v source)) (v source).denominator i := by
  have hs := denominatorPort_ge source
  simp (disch := omega) [seeded,prepareCall,clearMagnitude,afterInverseMagnitude,beforeInverse,
    NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    Function.update_apply,dataValues_small v hi,PhaseMachine.initialValues,magnitude]
  split_ifs <;> omega

theorem seeded_large (v : ℕ→Parts) (source i : ℕ) (hi : 1000 ≤ i) :
    seeded v source i=dataValues v i := by
  apply (values_unchanged (prepareCall source) _ i (by
    simp only [prepareCall,clearMagnitude,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with (h|h)|(h|h|h|h|h|h|h) <;>
      subst a <;> simp only [NatAssign.Instruction.target] <;> omega)).trans
  have h34 : i≠34 := by omega
  have h31 : i≠31 := by omega
  have h30 : i≠30 := by omega
  simp only [afterInverseMagnitude,beforeInverse,Function.update_of_ne h34,
    Function.update_of_ne h31,Function.update_of_ne h30]

#print axioms result_cos
#print axioms result_sin
#print axioms seeded_small
end Maxwell.Continuum.RationalDataflow.Phase
