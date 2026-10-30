import Maxwell.Continuum.PhaseMachineData
import Maxwell.Continuum.NatAssignOutputWidth
import Maxwell.Continuum.RationalTaylorProgram

/-! The fixed stored-word stages between Machin evaluation and Taylor evaluation. -/

namespace Maxwell.Continuum.PhaseMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
attribute [local irreducible] Machin.numeratorPositive Machin.numeratorNegative Machin.commonDenominator Machin.wordWidth

def ids : Finset ℕ := RationalTaylor.ids∪RationalMagnitude.ids∪{623,624,625,630,631}
def workspace : Finset ℕ := Machin.allWorkspace∪RationalMagnitude.workspace∪RationalTaylor.workspace∪{600,601,630,631}

def initialValues (a b i : ℕ) : ℕ := if i=630 then a else if i=631 then b else 0
def seedValues (a b Q N i : ℕ) : ℕ :=
  if i=623 then Machin.numeratorPositive (Calibration.phaseBits Q N) else
  if i=624 then Machin.numeratorNegative (Calibration.phaseBits Q N) else
  if i=625 then Machin.commonDenominator (Calibration.phaseBits Q N) else initialValues a b i

def beforeMagnitude (a b Q N : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (seedValues a b Q N) 30 (Machin.numeratorPositive (Calibration.phaseBits Q N)))
    31 (Machin.numeratorNegative (Calibration.phaseBits Q N))

def afterMagnitude (a b Q N : ℕ) : ℕ→ℕ :=
  Function.update (beforeMagnitude a b Q N) 34 (piMagnitude (Calibration.phaseBits Q N))

def prepareMagnitude : List NatAssign.Instruction := [.copy 623 30,.copy 624 31]
def prepareTaylor : List NatAssign.Instruction :=
  [.copy 34 600,.multiply 630 600,.literal 606 2,.multiply 606 600,.copy 625 601,.multiply 631 601]

def preparedValues (a b Q N : ℕ) : ℕ→ℕ := NatAssign.values prepareTaylor (afterMagnitude a b Q N)
def seedWidth (Q N W : ℕ) : ℕ := Machin.wordWidth (Calibration.phaseBits Q N)+W+4
def preparedWidth (Q N W : ℕ) : ℕ := 2^8*(seedWidth Q N W+1)
def stageCost (Q N W : ℕ) : ℕ := 2^50*(seedWidth Q N W+2)^2

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,RationalTaylor.ids,RationalMagnitude.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem stages_valid : (∀ i∈prepareMagnitude, i.Valid ids) ∧ (∀ i∈prepareTaylor, i.Valid ids) := by
  simp [prepareMagnitude,prepareTaylor,NatAssign.Instruction.Valid,ids,RationalTaylor.ids,RationalMagnitude.ids]

theorem prepareMagnitude_values (a b Q N : ℕ) :
    NatAssign.values prepareMagnitude (seedValues a b Q N)=beforeMagnitude a b Q N := by
  ext i
  simp [prepareMagnitude,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,beforeMagnitude,seedValues]

theorem beforeMagnitude_inputs (a b Q N : ℕ) :
    beforeMagnitude a b Q N 30=Machin.numeratorPositive (Calibration.phaseBits Q N) ∧
    beforeMagnitude a b Q N 31=Machin.numeratorNegative (Calibration.phaseBits Q N) ∧
    beforeMagnitude a b Q N 34=0 := by simp [beforeMagnitude,seedValues,initialValues]

theorem preparedValues_inputs (a b Q N : ℕ) :
    preparedValues a b Q N 600=argumentNumerator a Q N ∧
    preparedValues a b Q N 601=argumentDenominator b Q N := by
  simp [preparedValues,prepareTaylor,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,afterMagnitude,beforeMagnitude,seedValues,initialValues,
    argumentNumerator,argumentDenominator]
  constructor <;> ring

theorem seed_width (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) :
    (seedValues a b Q N i).bits.length≤seedWidth Q N W := by
  have hp := Machin.parts_width (Calibration.phaseBits Q N)
  unfold seedValues initialValues seedWidth
  split_ifs <;> first | omega | simp

theorem beforeMagnitude_width (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) :
    (beforeMagnitude a b Q N i).bits.length≤seedWidth Q N W := by
  have hp := Machin.parts_width (Calibration.phaseBits Q N)
  unfold beforeMagnitude
  by_cases h31 : i=31
  · subst i; simp only [Function.update_self]; exact hp.2.1.trans (by unfold seedWidth; omega)
  rw [Function.update_of_ne h31]
  by_cases h30 : i=30
  · subst i; simp only [Function.update_self]; exact hp.1.trans (by unfold seedWidth; omega)
  rw [Function.update_of_ne h30]
  exact seed_width a b Q N W ha hb i

theorem afterMagnitude_width (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) :
    (afterMagnitude a b Q N i).bits.length≤seedWidth Q N W := by
  unfold afterMagnitude
  by_cases h34 : i=34
  · subst i
    simp only [Function.update_self]
    have h := IntegerNormSquare.magnitude_bits_length_le
      (Machin.numeratorPositive (Calibration.phaseBits Q N)) (Machin.numeratorNegative (Calibration.phaseBits Q N))
    have hp := Machin.parts_width (Calibration.phaseBits Q N)
    exact h.trans (by unfold seedWidth; omega)
  rw [Function.update_of_ne h34]
  exact beforeMagnitude_width a b Q N W ha hb i

theorem prepared_width (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (i : ℕ) (hi : i∈ids) : (preparedValues a b Q N i).bits.length≤preparedWidth Q N W := by
  have hh := NatAssign.values_width_bound ids prepareTaylor stages_valid.2 (afterMagnitude a b Q N)
    (seedWidth Q N W) (fun i _ => afterMagnitude_width a b Q N W ha hb i)
    (by
      simp [prepareTaylor,NatAssign.Instruction.literalWidth]
      have htwo : (2:ℕ).bits.length=2 := by decide
      unfold seedWidth
      omega) i hi
  have hl : prepareTaylor.length=6 := rfl
  rw [hl] at hh
  unfold preparedValues preparedWidth
  omega

theorem stage_executes (Q N W : ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀ a∈ins, a.Valid ids) (hl : ins.length≤8)
    (hc : ∀ a∈ins, a.literalWidth≤2) (hf : NatAssign.changes ins⊆workspace)
    (v : ℕ→ℕ) (hw : ∀ i∈ids, (v i).bits.length≤seedWidth Q N W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code ins) cost s t ∧
      cost≤stageCost Q N W ∧ NatAssign.Bank ids (NatAssign.values ins v) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,hb,hsc',hframe⟩ := NatAssign.executes ids ids_ge ins hv v input tape s hs hsc
  have hp := NatAssign.price_bound ids ins hv v (seedWidth Q N W) hw
    (fun a ha => (hc a ha).trans (by unfold seedWidth; omega))
  have hcoef : 3000*8^ins.length≤(2:ℕ)^50 := by
    calc
      _ ≤ 3000*8^8 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_right (by decide) hl)
      _ ≤ _ := by norm_num
  exact ⟨cost,t,he,hcost.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),hb,hsc',hframe.mono hf⟩

#print axioms preparedValues_inputs
#print axioms prepared_width
#print axioms stage_executes

end Maxwell.Continuum.PhaseMachine
