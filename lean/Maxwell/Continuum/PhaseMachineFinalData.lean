import Maxwell.Continuum.MachinFinalBank
import Maxwell.Continuum.PhaseMachineProgram
import Maxwell.Continuum.RationalTaylorExtension

/-! Complete stored-word data for the phase evaluator. The full bank is
retained, including temporary Machin values, to charge repeated calls. -/
namespace Maxwell.Continuum.PhaseMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def allIds : Finset ℕ := ids∪Machin.allIds
def allWorkspace : Finset ℕ := {0,1,2,3}∪allIds

def fullSeed (a b Q N i : ℕ) : ℕ :=
  if i∈Machin.allIds then Machin.finalValues (Calibration.phaseBits Q N) i else initialValues a b i
def fullBefore (a b Q N : ℕ) : ℕ→ℕ := NatAssign.values prepareMagnitude (fullSeed a b Q N)
def fullAfter (a b Q N : ℕ) : ℕ→ℕ :=
  Function.update (fullBefore a b Q N) 34 (piMagnitude (Calibration.phaseBits Q N))
def fullPrepared (a b Q N : ℕ) : ℕ→ℕ := NatAssign.values prepareTaylor (fullAfter a b Q N)
def fullFinal (negative : Bool) (base : ℕ→Sign) (a b Q N : ℕ) : ℕ→ℕ :=
  RationalTaylor.extendedValues (fullPrepared a b Q N) (fractionSigns negative base) (order Q N)

def fullSeedWidth (Q N W : ℕ) : ℕ := Machin.finalWidth (Calibration.phaseBits Q N)+W+4
def fullWorkWidth (Q N W : ℕ) : ℕ := 2^12*(fullSeedWidth Q N W+2)
def fullFinalWidth (Q N W : ℕ) : ℕ := RationalTaylor.width (order Q N) (fullWorkWidth Q N W)

theorem allIds_ge (i : ℕ) (hi : i∈allIds) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hp|hm
  · exact ids_ge i hp
  · exact Machin.allIds_ge i hm

theorem allIds_small (i : ℕ) (hi : i∈allIds) : i<1000 := by
  simp only [allIds,ids,RationalTaylor.ids,RationalMagnitude.ids,Machin.allIds,
    RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem instruction_valid_all {a : NatAssign.Instruction} (h : a.Valid ids) : a.Valid allIds := by
  cases a with
  | literal target value => exact Finset.mem_union_left _ h
  | copy source target => exact ⟨Finset.mem_union_left _ h.1,Finset.mem_union_left _ h.2.1,h.2.2⟩
  | add source target => exact ⟨Finset.mem_union_left _ h.1,Finset.mem_union_left _ h.2.1,h.2.2⟩
  | multiply source target => exact ⟨Finset.mem_union_left _ h.1,Finset.mem_union_left _ h.2.1,h.2.2⟩

theorem fullSeed_inputs (a b Q N : ℕ) :
    fullSeed a b Q N 623=Machin.numeratorPositive (Calibration.phaseBits Q N) ∧
    fullSeed a b Q N 624=Machin.numeratorNegative (Calibration.phaseBits Q N) ∧
    fullSeed a b Q N 625=Machin.commonDenominator (Calibration.phaseBits Q N) ∧
    fullSeed a b Q N 630=a ∧ fullSeed a b Q N 631=b ∧ fullSeed a b Q N 34=0 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [fullSeed,ite_eq_left (by decide : 623∈Machin.allIds),Machin.finalValues] using
      (Machin.combine_values (Calibration.phaseBits Q N)).1
  · simpa only [fullSeed,ite_eq_left (by decide : 624∈Machin.allIds),Machin.finalValues] using
      (Machin.combine_values (Calibration.phaseBits Q N)).2.1
  · simpa only [fullSeed,ite_eq_left (by decide : 625∈Machin.allIds),Machin.finalValues] using
      (Machin.combine_values (Calibration.phaseBits Q N)).2.2
  · simp only [fullSeed,ite_eq_right (by decide : 630∉Machin.allIds),initialValues,↓reduceIte]
  · simp [fullSeed,initialValues,Machin.allIds,RationalArctan.ids]
  · simp [fullSeed,initialValues,Machin.allIds,RationalArctan.ids]

theorem fullBefore_inputs (a b Q N : ℕ) :
    fullBefore a b Q N 30=Machin.numeratorPositive (Calibration.phaseBits Q N) ∧
    fullBefore a b Q N 31=Machin.numeratorNegative (Calibration.phaseBits Q N) ∧
    fullBefore a b Q N 34=0 := by
  have h := fullSeed_inputs a b Q N
  simpa only [fullBefore,prepareMagnitude,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_self,
    Function.update_of_ne (by decide : (30 : ℕ)≠31),Function.update_of_ne (by decide : (34 : ℕ)≠31),
    Function.update_of_ne (by decide : (34 : ℕ)≠30),Function.update_of_ne (by decide : (624 : ℕ)≠30)] using
    And.intro h.1 (And.intro h.2.1 h.2.2.2.2.2)

theorem fullPrepared_inputs (a b Q N : ℕ) :
    fullPrepared a b Q N 600=argumentNumerator a Q N ∧
    fullPrepared a b Q N 601=argumentDenominator b Q N := by
  have h := fullSeed_inputs a b Q N
  simp only [fullPrepared,prepareTaylor,fullAfter,fullBefore,prepareMagnitude,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    Function.update_apply]
  norm_num only [↓reduceIte]
  rw [h.2.2.1,h.2.2.2.1,h.2.2.2.2.1]
  unfold argumentNumerator argumentDenominator
  constructor <;> ring

theorem fullSeed_width (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (i : ℕ) : (fullSeed a b Q N i).bits.length≤fullSeedWidth Q N W := by
  unfold fullSeed
  split_ifs with hi
  · exact (Machin.finalValues_width _ i hi).trans (by unfold fullSeedWidth;omega)
  · unfold initialValues fullSeedWidth
    split_ifs <;> first | omega | simp

theorem fullBefore_width (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (i : ℕ) (hi : i∈allIds) :
    (fullBefore a b Q N i).bits.length≤4*(fullSeedWidth Q N W+1) := by
  have h := NatAssign.values_width_bound allIds prepareMagnitude
    (fun x hx => instruction_valid_all (stages_valid.1 x hx))
    (fullSeed a b Q N) (fullSeedWidth Q N W) (fun k _ => fullSeed_width a b Q N W ha hb k)
    (by simp [prepareMagnitude,NatAssign.Instruction.literalWidth]) i hi
  exact (Nat.le_add_right _ 1).trans h

theorem fullAfter_width (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (i : ℕ) (hi : i∈allIds) :
    (fullAfter a b Q N i).bits.length≤4*(fullSeedWidth Q N W+1)+1 := by
  by_cases he : i=34
  · subst i
    simp only [fullAfter,Function.update_self,piMagnitude]
    have hp := Machin.parts_width (Calibration.phaseBits Q N)
    have hf := Machin.finalValues_width (Calibration.phaseBits Q N)
    have hn := hf 623 (by decide)
    have hm := hf 624 (by decide)
    rw [Machin.finalValues,(Machin.combine_values _).1] at hn
    rw [Machin.finalValues,(Machin.combine_values _).2.1] at hm
    apply (IntegerNormSquare.magnitude_bits_length_le _ _).trans
    unfold fullSeedWidth
    omega
  · simpa only [fullAfter,Function.update_of_ne he] using
      (fullBefore_width a b Q N W ha hb i hi).trans (Nat.le_succ _)

theorem fullPrepared_width (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (i : ℕ) (hi : i∈allIds) :
    (fullPrepared a b Q N i).bits.length≤fullWorkWidth Q N W := by
  have h := NatAssign.values_width_bound allIds prepareTaylor
    (fun x hx => instruction_valid_all (stages_valid.2 x hx))
    (fullAfter a b Q N) (4*(fullSeedWidth Q N W+1)+1)
    (fullAfter_width a b Q N W ha hb)
    (by
      have ht : (2 : ℕ).bits.length=2 := by decide
      simp [prepareTaylor,NatAssign.Instruction.literalWidth,ht]
      omega) i hi
  have hl : prepareTaylor.length=6 := rfl
  rw [hl] at h
  unfold fullPrepared fullWorkWidth
  omega

theorem fullFinal_width (negative : Bool) (base : ℕ→Sign) (a b Q N W : ℕ)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) (hi : i∈allIds) :
    (fullFinal negative base a b Q N i).bits.length≤fullFinalWidth Q N W :=
  RationalTaylor.extended_width allIds (by decide) (fullPrepared a b Q N)
    (fractionSigns negative base) (order Q N) (fullWorkWidth Q N W)
    (fullPrepared_width a b Q N W ha hb) i hi

#print axioms fullPrepared_inputs
#print axioms fullFinal_width
end Maxwell.Continuum.PhaseMachine
