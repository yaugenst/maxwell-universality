import Maxwell.Continuum.ParameterBufferMachineAdvance
import Maxwell.Continuum.ParameterBufferMachinePredicate
import Maxwell.Continuum.NaturalBankQuotient
import Maxwell.Cost.RoutingPorts.Primitives

namespace Maxwell.Continuum.Parameters.BufferMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
open RationalAccumulator (Blank Word)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] values width

def workspace : Finset ℕ := extra∪Compare.workspace∪{4}
def testCode : Code := AllComparisons.code tests
def testCost (W : ℕ) : ℕ := tests.length*(AllComparisons.unitCost W+2)+2

def Ready (D : Data) (k W : ℕ) (s : Store) : Prop :=
  ∃v,NatAssign.Bank ids v s.val ∧ (∀i,i<5→Blank s.val i) ∧
    (∀i∈extra,v i=values D k i) ∧ (∀i∈ids,(v i).bits.length ≤ W) ∧ v 35=0 ∧ v 36=0

theorem tests_enabled (D : Data) (k : ℕ) (hKd : 0<D.conditionDen) (hAn : 0<D.alphaNum)
    (hTn : 0<D.tauNum) (hEn : 0<D.epsilonNum) :
    ∀q∈tests,AllComparisons.Enabled (values D k) q := by
  have hd := (fields D k).2.2
  have h1 : values D k 2120=1 := by simpa [inputs] using input_fields D k 2120 (by decide)
  simp only [tests,List.mem_cons,List.not_mem_nil,or_false]
  intro q hq
  subst q
  simp only [AllComparisons.Enabled,hd,h1,denominator]
  constructor <;> positivity

theorem test_executes (D : Data) (k W : ℕ) (hKd : 0<D.conditionDen) (hAn : 0<D.alphaNum)
    (hTn : 0<D.tauNum) (hEn : 0<D.epsilonNum)
    (input : List Bool) (randomTape : ℕ→Bool) (s : Store) (hs : Ready D k W s) :
    ∃cost t,Executes input randomTape testCode cost s t ∧ cost ≤ testCost W ∧ Ready D k W t ∧
      t.val.registers 35=tests.any (AllComparisons.failed (values D k)) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨v,hb,hsc,hv,hw,h35,h36⟩ := hs
  have hen : ∀q∈tests,AllComparisons.Enabled v q := by
    intro q hq
    have ht := tests_valid q hq
    simpa only [AllComparisons.Enabled,hv q.1.2 ht.2.1,hv q.2.2 ht.2.2.2] using
      tests_enabled D k hKd hAn hTn hEn q hq
  obtain ⟨cost,t,w,he,hc,hr,bt,st,wv,ww,w35,w36,hf⟩ := AllComparisons.executes extra
    (by intro i hi;simp only [extra,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,
      Finset.mem_singleton] at hi;omega) tests tests_valid v W hw hen h35 h36 input randomTape s hb
    (fun i hi=>hsc i (by omega))
  refine ⟨cost,t,he,hc,⟨w,bt,?_,fun i hi=>(wv i hi).trans (hv i hi),ww,w35,w36⟩,
    hr.trans (AllComparisons.failures_congr extra tests tests_valid v _ hv),hf.mono (by decide +kernel)⟩
  intro i hi
  by_cases h : i<4
  · exact st i h
  · have hi4 : i=4 := by omega
    subst i
    exact RationalAccumulator.blank_of_eq (hf.tapes 4 (by decide)) (hsc 4 (by decide))

theorem nat_frame {s t : BitRAMState} (h : BinaryPrecision.Frame ({0,1,2,3}∪ids) s t) :
    BinaryPrecision.Frame workspace s t := h.mono (by decide +kernel)

theorem quotient_frame {s t : BitRAMState} (h : BinaryPrecision.Frame ({0,1,2,3,4}∪ids) s t) :
    BinaryPrecision.Frame workspace s t := h.mono (by decide +kernel)

theorem extra_inputs_width (D : Data) (k N B : ℕ) (hk : k ≤ N) (hD : D.Width B) (i : ℕ) :
    (inputs D k i).bits.length ≤ width N B := by
  have hi := inputs_width D k N B hk hD i
  have hmul := Nat.le_mul_of_pos_left (inputWidth N B+1) (Nat.two_pow_pos formulas.length)
  exact hi.trans (by unfold width;omega)

/-- An arithmetic stage uses four scratch words; the fifth belongs to the
subsequent exact division and is carried through unchanged. -/
theorem fifth_scratch {s t : BitRAMState} (h : BinaryPrecision.Frame ({0,1,2,3}∪ids) s t)
    (hs : ∀i,i<5→Blank s i) (ht : NatAssign.Scratch t) : ∀i,i<5→Blank t i := by
  intro i hi
  by_cases h4 : i<4
  · exact ht i h4
  · have hi4 : i=4 := by omega
    subst i
    exact RationalAccumulator.blank_of_eq (h.tapes 4 (by decide +kernel)) (hs 4 (by decide))

#print axioms test_executes
end Maxwell.Continuum.Parameters.BufferMachine
