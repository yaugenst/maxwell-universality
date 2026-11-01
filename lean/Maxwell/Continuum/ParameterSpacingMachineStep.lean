import Maxwell.Continuum.ParameterSpacingMachineAdvance
import Maxwell.Continuum.ParameterSpacingMachinePredicate

namespace Maxwell.Continuum.Parameters.SpacingMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] values width

def workspace : Finset ℕ := extra∪Compare.workspace
def stepInstructions := advance++formulas
def stepCode : Code := NatAssign.code stepInstructions
def testCode : Code := AllComparisons.code tests
def testCost (W : ℕ) : ℕ := tests.length*(AllComparisons.unitCost W+2)+2
def stepCost (W : ℕ) : ℕ := 3000*8^stepInstructions.length*(W+2)^2

def Ready (D : Data) (k W : ℕ) (s : Store) : Prop :=
  ∃ v, NatAssign.Bank ids v s.val ∧ NatAssign.Scratch s.val ∧
    (∀ i ∈ extra, v i=values D k i) ∧ (∀ i ∈ ids, (v i).bits.length≤W) ∧
    v 35=0 ∧ v 36=0

theorem tests_enabled (D : Data) (k : ℕ) (hKn : 0<D.conditionNum) (hEd : 0<D.epsilonDen) :
    ∀ q ∈ tests, AllComparisons.Enabled (values D k) q := by
  obtain ⟨h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31⟩ := fields D k
  have h09 : values D k 2009=1 := by simpa [inputs] using input_fields D k 2009 (by decide)
  have h07 : values D k 2007=3^(2^k) := by simpa [inputs] using input_fields D k 2007 (by decide)
  simp only [tests,List.mem_cons,List.not_mem_nil,or_false]
  intro q hq
  rcases hq with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [AllComparisons.Enabled,h09,h07,h25,h27,h28,h30]
  all_goals constructor <;> positivity

theorem test_executes (D : Data) (k W : ℕ) (hKn : 0<D.conditionNum) (hEd : 0<D.epsilonDen)
    (input : List Bool) (randomTape : ℕ→Bool) (s : Store) (hs : Ready D k W s) :
    ∃ cost t, Executes input randomTape testCode cost s t ∧ cost≤testCost W ∧ Ready D k W t ∧
      t.val.registers 35=tests.any (AllComparisons.failed (values D k)) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨v,hb,hsc,hv,hw,h35,h36⟩ := hs
  have hen : ∀ q ∈ tests, AllComparisons.Enabled v q := by
    intro q hq
    have ht := tests_valid q hq
    simpa only [AllComparisons.Enabled,hv q.1.2 ht.2.1,hv q.2.2 ht.2.2.2] using
      tests_enabled D k hKn hEd q hq
  obtain ⟨cost,t,w,he,hc,hr,bt,st,wv,ww,w35,w36,hf⟩ := AllComparisons.executes extra
    (by intro i hi;simp only [extra,Finset.mem_Icc] at hi;omega) tests tests_valid
    v W hw hen h35 h36 input randomTape s hb hsc
  exact ⟨cost,t,he,hc,⟨w,bt,st,fun i hi => (wv i hi).trans (hv i hi),ww,w35,w36⟩,
    hr.trans (AllComparisons.failures_congr extra tests tests_valid v _ hv),
    hf.mono (Finset.subset_union_right)⟩

theorem step_extra_valid : ∀ a ∈ stepInstructions, a.Valid extra := by
  intro a ha
  rcases List.mem_append.mp ha with ha|ha
  · exact advance_valid a ha
  · exact formulas_extra_valid a ha

theorem step_valid : ∀ a ∈ stepInstructions, a.Valid ids := by
  intro a ha
  have h := step_extra_valid a ha
  cases a <;> simp only [NatAssign.Instruction.Valid] at h ⊢
  all_goals simp_all [ids,Compare.ids]

theorem step_executes (D : Data) (k N B : ℕ) (hk : k+1≤N) (hD : D.Width B)
    (input : List Bool) (randomTape : ℕ→Bool) (s : Store) (hs : Ready D k (width N B) s) :
    ∃ cost t, Executes input randomTape stepCode cost s t ∧ cost≤stepCost (width N B) ∧
      Ready D (k+1) (width N B) t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨v,hb,hsc,hv,hw,h35,h36⟩ := hs
  obtain ⟨cost,t,he,hc,bt,st,hf⟩ := NatAssign.executes ids ids_ge stepInstructions step_valid
    v input randomTape s hb hsc
  have hp := NatAssign.price_bound ids stepInstructions step_valid v (width N B) hw
    (by simp [stepInstructions,advance,formulas,List.range_succ,NatAssign.Instruction.literalWidth])
  let w := NatAssign.values stepInstructions v
  have wn : ∀ i ∈ extra, w i=values D (k+1) i := next_values D k v hv
  have wo (i : ℕ) (hi : i∉extra) : w i=v i :=
    NatAssign.values_outside extra stepInstructions step_extra_valid v i hi
  refine ⟨cost,t,he,hc.trans hp,⟨w,bt,st,wn,?_,?_,?_⟩,
    hf.mono (by decide +kernel)⟩
  · intro i hi
    by_cases hie : i∈extra
    · rw [wn i hie]
      exact values_width D (k+1) N B hk hD i hi
    · rw [wo i hie]
      exact hw i hi
  · exact (wo 35 (by decide)).trans h35
  · exact (wo 36 (by decide)).trans h36

#print axioms test_executes
#print axioms step_executes

end Maxwell.Continuum.Parameters.SpacingMachine
