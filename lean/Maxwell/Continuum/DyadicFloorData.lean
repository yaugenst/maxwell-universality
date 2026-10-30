import Maxwell.Continuum.NaturalBankQuotient
import Maxwell.Continuum.NatAssignCleanup
import Maxwell.Continuum.DyadicRounding
import Maxwell.Continuum.RationalDataflowProgram

/-! Exact signed floor via one nonnegative natural division.
The shift by the negative numerator is integral and avoids a signed
division branch, including when the input is an unreduced rational. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def scaledPositive (P : ℕ) (x : Parts) : ℕ := x.positive*2^P
def scaledNegative (P : ℕ) (x : Parts) : ℕ := x.negative*2^P
def shiftedPositive (P : ℕ) (x : Parts) : ℕ := scaledPositive P x+scaledNegative P x*x.denominator
def nonnegativeNumerator (P : ℕ) (x : Parts) : ℕ := shiftedPositive P x-scaledNegative P x
def result (P : ℕ) (x : Parts) : Parts :=
  ⟨nonnegativeNumerator P x/x.denominator,scaledNegative P x,1⟩

theorem shifted_le (P : ℕ) (x : Parts) (hx : x.Valid) : scaledNegative P x≤shiftedPositive P x := by
  change 0<x.denominator at hx
  have h := Nat.mul_le_mul_left (scaledNegative P x) (by omega : 1≤x.denominator)
  unfold shiftedPositive
  omega

theorem magnitude_eq (P : ℕ) (x : Parts) (hx : x.Valid) :
    IntegerNormSquare.magnitude (shiftedPositive P x) (scaledNegative P x)=nonnegativeNumerator P x :=
  Parts.magnitude_eq_of_le ⟨shiftedPositive P x,scaledNegative P x,1⟩ (shifted_le P x hx)

theorem nonnegativeNumerator_value (P : ℕ) (x : Parts) (hx : x.Valid) :
    (nonnegativeNumerator P x:ℚ)/x.denominator-(scaledNegative P x:ℚ)=x.value*(2:ℚ)^P := by
  have hd : (x.denominator:ℚ)≠0 := by exact_mod_cast hx.ne'
  rw [nonnegativeNumerator,Nat.cast_sub (shifted_le P x hx)]
  unfold shiftedPositive scaledPositive scaledNegative Parts.value
  push_cast
  field_simp
  ring

theorem result_value (P : ℕ) (x : Parts) (hx : x.Valid) :
    (result P x).value=((roundDyadic P x.value).numerator:ℚ) := by
  have he := nonnegativeNumerator_value P x hx
  unfold roundDyadic
  rw [←he,Int.floor_sub_natCast,Rat.floor_natCast_div_natCast]
  simp only [result,Parts.value,Nat.cast_one,div_one,Int.cast_sub,Int.ofNat_ediv_ofNat,Int.cast_natCast]

theorem result_valid (P : ℕ) (x : Parts) : (result P x).Valid := by
  exact Nat.zero_lt_one

def privateTapes : List ℕ := [30,31,32,33,34,35,36,140,142,143]
def extraIds : Finset ℕ := {140,142,143}
def allIds (S : Finset ℕ) : Finset ℕ := ids S∪extraIds∪NaturalQuotient.workPorts
def workspace (S : Finset ℕ) : Finset ℕ := {0,1,2,3,4}∪allIds S
def Clean (s : BitRAMState) : Prop :=
  RationalAccumulator.Blank s 4 ∧ ∀i∈extraIds∪NaturalQuotient.workPorts,RationalAccumulator.Blank s i

def prepare (P source : ℕ) : List NatAssign.Instruction :=
  [.literal 143 (2^P),.copy (positivePort source) 30,.multiply 143 30,
   .copy (negativePort source) 31,.multiply 143 31,.copy 31 140,
   .multiply (denominatorPort source) 140,.add 140 30,.literal 140 0,
   .copy (denominatorPort source) 142]
def beforeMagnitude (P : ℕ) (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (Function.update (Function.update (dataValues v)
    30 (shiftedPositive P (v source))) 31 (scaledNegative P (v source)))
      142 (v source).denominator) 143 (2^P)
def afterMagnitude (P : ℕ) (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  Function.update (beforeMagnitude P v source) 34 (nonnegativeNumerator P (v source))
def divided (P : ℕ) (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  Function.update (afterMagnitude P v source) 140 (nonnegativeNumerator P (v source)/(v source).denominator)
def output (target : ℕ) : List NatAssign.Instruction :=
  [.copy 140 (positivePort target),.copy 31 (negativePort target),.literal (denominatorPort target) 1]
def finish (target : ℕ) : List NatAssign.Instruction := output target++NatAssign.clearList privateTapes
def code (P target source : ℕ) : Code :=
  .seq (NatAssign.code (prepare P source))
    (.seq RationalMagnitude.program
      (.seq (NaturalQuotient.code 34 142 140) (NatAssign.code (finish target))))

theorem prepare_values (P : ℕ) (v : ℕ→Parts) (source : ℕ) :
    NatAssign.values (prepare P source) (dataValues v)=beforeMagnitude P v source := by
  have hp := positivePort_ge source
  have hn := negativePort_ge source
  have hd := denominatorPort_ge source
  ext i
  simp (disch := omega) [prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,beforeMagnitude,
    shiftedPositive,scaledPositive,scaledNegative,Function.update_apply,Nat.mul_comm,Nat.add_comm]
  split_ifs <;> simp_all [dataValues_small]

theorem beforeMagnitude_inputs (P : ℕ) (v : ℕ→Parts) (source : ℕ) :
    beforeMagnitude P v source 30=shiftedPositive P (v source) ∧
    beforeMagnitude P v source 31=scaledNegative P (v source) ∧
    beforeMagnitude P v source 34=0 ∧ beforeMagnitude P v source 142=(v source).denominator := by
  simp [beforeMagnitude,dataValues_small]

theorem finish_values (P : ℕ) (v : ℕ→Parts) (target source : ℕ) :
    NatAssign.values (finish target) (divided P v source)=dataValues (Function.update v target (result P (v source))) := by
  rw [finish,values_append,←writeParts_dataValues]
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  ext i
  rw [NatAssign.clearList_values]
  by_cases hs : i<1000
  · simp (disch := omega) [privateTapes,output,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,divided,afterMagnitude,beforeMagnitude,
      result,writeParts,Function.update_apply,dataValues_small v hs]
    split_ifs <;> simp_all
  · simp (disch := omega) [privateTapes,output,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,divided,afterMagnitude,beforeMagnitude,
      result,writeParts,Function.update_apply]
    intro hi
    omega

#print axioms result_value
#print axioms prepare_values
#print axioms finish_values
end Maxwell.Continuum.RationalDataflow.DyadicFloor
