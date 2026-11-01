import Maxwell.Continuum.RationalDataflowResetInvariant
import Maxwell.Continuum.RationalDataflowArray

/-! A rational scratch reset carried through a larger natural-word bank.
The retained words keep their width; reset words receive actual literal zeros. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def resetNaturalValues (S : Finset ℕ) (xs : List ℕ) (n : ℕ → ℕ) (v : ℕ → Parts) (k : ℕ) : ℕ :=
  if k∈ids S then dataValues ((resetList xs).evaluate v) k else n k

theorem resetNatural_executes (S allIds : Finset ℕ) (xs : List ℕ)
    (hIds : ∀k∈allIds,4≤k) (hxs : ∀k∈xs,k∈S)
    (n : ℕ → ℕ) (v : ℕ → Parts) (U B : ℕ) (hB : 1≤B) (hBU : B≤U)
    (hw : ∀k∈allIds,(n k).bits.length≤U) (width : WidthBank S U v) (hg : Good S v)
    (retained : ∀k∈S,k∉xs → (v k).Width B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (ready : Ready S v s) (four : RationalAccumulator.Blank s.val 4) :
    ∃cost t,Executes input tape (resetList xs).code cost s t ∧
      cost≤xs.length*operationCost U+1 ∧ Ready S ((resetList xs).evaluate v) t ∧
      Good S ((resetList xs).evaluate v) ∧ WidthBank S B ((resetList xs).evaluate v) ∧
      NatAssign.Bank allIds (resetNaturalValues S xs n v) t.val ∧
      (∀k∈allIds,(resetNaturalValues S xs n v k).bits.length≤U) ∧
      RationalAccumulator.Blank t.val 4 ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,e,hc,rt,frame⟩ := resetList_executes S xs hxs v U (by omega) width hg input tape s ready
  have good := (resetList xs).evaluate_good S (resetList_valid S xs hxs) v hg (resetList_admissible xs v)
  have outputWidth := resetList_result_width S xs v B hB retained
  have naturalBank : NatAssign.Bank allIds (resetNaturalValues S xs n v) t.val := by
    intro k hk
    by_cases hp : k∈ids S
    · simpa only [resetNaturalValues,ite_eq_left hp] using rt.1 k hp
    · have external : k∉workspace S := by
        have hge := hIds k hk
        simp only [workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨by omega,hp⟩
      simpa only [resetNaturalValues,ite_eq_right hp] using RationalAccumulator.word_of_eq (frame.tapes k external) (hs k hk)
  have rawWidth : ∀k∈allIds,(resetNaturalValues S xs n v k).bits.length≤U := by
    intro k hk
    by_cases hp : k∈ids S
    · rw [resetNaturalValues,ite_eq_left hp]
      exact dataValues_width S _ U (outputWidth.mono hBU) k hp
    · rw [resetNaturalValues,ite_eq_right hp]
      exact hw k hk
  have hids : 4∉ids S := fun h => by have := ids_ge_ten S 4 h;omega
  exact ⟨cost,t,e,hc,rt,good,outputWidth,naturalBank,rawWidth,
    RationalAccumulator.blank_of_eq (frame.tapes 4 (by simp [workspace,hids])) four,frame⟩

#print axioms resetNatural_executes
end Maxwell.Continuum.RationalDataflow
