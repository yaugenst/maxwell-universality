import Maxwell.Cost.Structured.Primitive
import Maxwell.Cost.Counter
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Maxwell.Cost.Structured.Counted

open scoped BigOperators

def test (countTape : ℕ) : Code :=
  .seq (.call (Counter.programOn countTape)) (Code.atom (.bitNot 29 2))

/-- The counter tape is a literal parameter in finite syntax. Nested loops
use distinct tapes; the body's code cannot be selected by a host callback. -/
def code (countTape : ℕ) (body : Code) : Code :=
  .seq (test countTape) (.loop 29 (.seq body (test countTape)))

def Frame (countTape : ℕ) (s t : Store) : Prop :=
  t.val.address = s.val.address ∧ t.val.inputHead = s.val.inputHead ∧
  t.val.memory = s.val.memory ∧ t.val.randomCursor = s.val.randomCursor ∧
  t.val.output = s.val.output ∧
  (∀ i, i ≠ countTape → t.val.tapes i = s.val.tapes i) ∧
  (∀ i, 4 < i → i ≠ 24 → i ≠ 25 → i ≠ 29 → t.val.registers i = s.val.registers i)

theorem test_executes (countTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (xs : List Bool) (hword : s.val.tapes countTape = BitTape.ofList xs) :
    ∃ t, Executes input randomTape (test countTape) (13 * xs.length + 14) s t ∧
      t.val.tapes countTape = BitTape.ofList (subtractBit true xs) ∧
      (t.val.registers 29 = false ↔ addressValue xs = 0) ∧ Frame countTape s t := by
  obtain ⟨middle, hs, hp, _, hw, hz, _, hf⟩ :=
    Counter.steps_on countTape input randomTape xs s.val s.property hword
  have hh : (Counter.programOn countTape).code[middle.pc]? = some .halt := by
    simp [Counter.programOn, BitRAM.renameTapes, hp, Counter.program, BitRAM.link,
      Counter.counterSuffix, binaryCounter, Rewind.program, BitRAMInstruction.relocate,
      BitRAMInstruction.renameTapes]
  have hc := Executes.call (Counter.programOn countTape) s middle _ hs hh
  have hn := Executes.bitNot input randomTape (Store.ofState middle) 29 2
  let t := Store.ofState ((Store.ofState middle).val.setRegister 29
    (!(Store.ofState middle).val.registers 2))
  refine ⟨t, ?_, hw, ?_, ?_⟩
  · convert hc.seq hn using 1
    simp [test]
  · simpa [t, Store.ofState, BitRAMState.setRegister] using hz
  · rcases hf with ⟨ha, hi, hm, hr, ho, ht, hg⟩
    refine ⟨ha, hi, hm, hr, ho, ht, ?_⟩
    intro i hi h24 h25 h29
    simpa [t, Store.ofState, BitRAMState.setRegister, h29] using hg i hi h24 h25

/-- Generic finite countdown with a semantic invariant. The invariant must
survive the explicitly stated counter scratch effects. The body is always
one fixed `Code` value and must preserve the actual remaining counter word. -/
theorem executes (countTape : ℕ) (body : Code) (input : List Bool) (randomTape : ℕ → Bool)
    (invariant : ℕ → Store → Prop) (bound : ℕ → ℕ)
    (stable : ∀ n s t, Frame countTape s t → invariant n s → invariant n t)
    (bodyCorrect : ∀ n xs s, invariant (n + 1) s →
      s.val.tapes countTape = BitTape.ofList xs → addressValue xs = n →
      ∃ bodyCost t, Executes input randomTape body bodyCost s t ∧
        invariant n t ∧ t.val.tapes countTape = BitTape.ofList xs ∧ bodyCost ≤ bound n)
    (n : ℕ) (xs : List Bool) (s : Store) (hvalue : addressValue xs = n)
    (hword : s.val.tapes countTape = BitTape.ofList xs) (hinvariant : invariant n s) :
    ∃ cost t finalWord, Executes input randomTape (code countTape body) cost s t ∧
      invariant 0 t ∧ t.val.tapes countTape = BitTape.ofList finalWord ∧
      finalWord.length = xs.length ∧ t.val.registers 29 = false ∧
      cost ≤ (n + 1) * (13 * xs.length + 15) + ∑ k ∈ Finset.range n, bound k := by
  induction n generalizing xs s with
  | zero =>
    obtain ⟨t, ht, hw, hz, hf⟩ := test_executes countTape input randomTape s xs hword
    have hfalse := hz.mpr hvalue
    refine ⟨13 * xs.length + 14 + 1, t, subtractBit true xs,
      ht.seq (Executes.done hfalse), stable 0 s t hf hinvariant, hw,
      subtractBit_length true xs, hfalse, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨tested, htest, hw, hz, hf⟩ := test_executes countTape input randomTape s xs hword
    have hpositive : 0 < addressValue xs := by omega
    have hdecrease : addressValue (subtractBit true xs) = n := by
      rw [subtractBit_pred xs hpositive, hvalue]
      omega
    have htrue : tested.val.registers 29 = true := by
      cases hb : tested.val.registers 29 with
      | true => rfl
      | false => have := hz.mp hb; omega
    obtain ⟨bodyCost, middle, hbody, hmInv, hmWord, hmCost⟩ :=
      bodyCorrect n (subtractBit true xs) tested (stable (n + 1) s tested hf hinvariant) hw hdecrease
    obtain ⟨restCost, t, finalWord, hrest, htInv, htWord, htLength, htFalse, htCost⟩ :=
      ih (subtractBit true xs) middle hdecrease hmWord hmInv
    change Executes input randomTape (.seq (test countTape) (.loop 29 (.seq body (test countTape))))
      restCost middle t at hrest
    cases hrest with
    | seq restTest restLoop =>
      refine ⟨_, t, finalWord, htest.seq (Executes.more htrue (hbody.seq restTest) restLoop),
        htInv, htWord, htLength.trans (subtractBit_length true xs), htFalse, ?_⟩
      simp only [subtractBit_length] at htCost
      rw [Finset.sum_range_succ]
      nlinarith

end Maxwell.Cost.Structured.Counted
