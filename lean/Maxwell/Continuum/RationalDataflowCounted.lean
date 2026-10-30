import Maxwell.Continuum.RationalDataflowControl
import Maxwell.Cost.Structured.CountedShifted

/-! Uniform runtime repetition: the loop count is a stored word, not generated code. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem Ready.count_frame (S : Finset ℕ) (v : ℕ→Parts) (countTape : ℕ)
    (hc : countTape∉workspace S) {s t : Store} (hs : Ready S v s)
    (hf : CountedShifted.Frame countTape s t) : Ready S v t := by
  constructor
  · intro i hi
    have hne : i≠countTape := by
      intro he
      subst i
      exact hc (Finset.mem_union_right _ hi)
    exact RationalAccumulator.word_of_eq (hf.2.2.2.2.2.1 i hne) (hs.1 i hi)
  · intro i hi
    have hne : i≠countTape := by
      intro he
      subst i
      apply hc
      apply Finset.mem_union_left
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    exact RationalAccumulator.blank_of_eq (hf.2.2.2.2.2.1 i hne) (hs.2 i hi)

def countedProgram (countTape : ℕ) (body : Code) : Code := CountedShifted.code countTape body

theorem counted_executes (S : Finset ℕ) (countTape : ℕ) (hc : countTape∉workspace S)
    (body : Code) (n stepCost : ℕ) (states : ℕ→(ℕ→Parts))
    (input : List Bool) (tape : ℕ→Bool)
    (hbody : ∀ k<n, ∀ s : Store, Ready S (states k) s →
      ∃ cost t, Executes input tape body cost s t ∧ cost≤stepCost ∧
        Ready S (states (k+1)) t ∧ BinaryPrecision.Frame (workspace S) s.val t.val)
    (xs : List Bool) (origin : ℤ) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes countTape=BitTape.shifted xs origin) (hs : Ready S (states 0) s) :
    ∃ cost t finalWord, Executes input tape (countedProgram countTape body) cost s t ∧
      Ready S (states n) t ∧ t.val.tapes countTape=BitTape.shifted finalWord origin ∧
      finalWord.length=xs.length ∧
      cost≤(n+1)*(13*xs.length+15)+n*stepCost := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤n ∧ Ready S (states (n-remaining)) st
  have stable : ∀ remaining a b, CountedShifted.Frame countTape a b → inv remaining a → inv remaining b := by
    intro remaining a b hf hh
    exact ⟨hh.1,Ready.count_frame S _ countTape hc hh.2 hf⟩
  have hstep : ∀ remaining ys a, inv (remaining+1) a →
      a.val.tapes countTape=BitTape.shifted ys origin → addressValue ys=remaining →
      ∃ cost b, Executes input tape body cost a b ∧ inv remaining b ∧
        b.val.tapes countTape=BitTape.shifted ys origin ∧ cost≤stepCost := by
    intro remaining ys a ha hword _
    have hk : n-(remaining+1)<n := by have := ha.1; omega
    obtain ⟨cost,b,he,hbound,hb,hf⟩ := hbody (n-(remaining+1)) hk a ha.2
    have heq : n-(remaining+1)+1=n-remaining := by have := ha.1; omega
    rw [heq] at hb
    exact ⟨cost,b,he,⟨by have := ha.1; omega,hb⟩,(hf.tapes countTape hc).trans hword,hbound⟩
  obtain ⟨cost,t,finalWord,he,ht,hword,hlen,_,hbound⟩ :=
    CountedShifted.executes countTape origin body input tape inv (fun _ => stepCost)
      stable hstep n xs s hn hcount ⟨le_rfl,by simpa [inv] using hs⟩
  refine ⟨cost,t,finalWord,he,?_,hword,hlen,?_⟩
  · simpa only [Nat.sub_zero] using ht.2
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hbound

def iterateControl (c : Control) (v : ℕ→Parts) : ℕ→(ℕ→Parts)
  | 0 => v
  | n+1 => c.evaluate (iterateControl c v n)

theorem controlCounted_executes (S : Finset ℕ) (countTape : ℕ) (hc : countTape∉workspace S)
    (c : Control) (hv : c.Valid S) (n B : ℕ) (v : ℕ→Parts)
    (hw : ∀ k<n, c.WidthTrace S B (iterateControl c v k))
    (hg : ∀ k<n, Good S (iterateControl c v k))
    (ha : ∀ k<n, c.AdmissibleTrace (iterateControl c v k))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue xs=n) (hcount : s.val.tapes countTape=BitTape.shifted xs origin)
    (hs : Ready S v s) :
    ∃ cost t finalWord, Executes input tape (countedProgram countTape c.code) cost s t ∧
      Ready S (iterateControl c v n) t ∧ t.val.tapes countTape=BitTape.shifted finalWord origin ∧
      finalWord.length=xs.length ∧
      cost≤(n+1)*(13*xs.length+15)+n*(c.steps*operationCost B+1) := by
  apply counted_executes S countTape hc c.code n (c.steps*operationCost B+1) (iterateControl c v)
    input tape ?_ xs origin s hn hcount hs
  intro k hk a hready
  exact c.executes S hv _ B (hw k hk) (hg k hk) (ha k hk) input tape a hready

theorem controlCounted_computes (S : Finset ℕ) (countTape : ℕ) (hc : countTape∉workspace S)
    (c : Control) (hv : c.Valid S) (n B : ℕ) (v : ℕ→Parts)
    (hw : ∀ k<n, c.WidthTrace S B (iterateControl c v k))
    (hg : ∀ k<n, Good S (iterateControl c v k))
    (ha : ∀ k<n, c.AdmissibleTrace (iterateControl c v k))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue xs=n) (hcount : s.val.tapes countTape=BitTape.shifted xs origin)
    (hs : Ready S v s) :
    ∃ cost t,
      (runPriced ((countedProgram countTape c.code).compile.next input tape)
        ((n+1)*(13*xs.length+15)+n*(c.steps*operationCost B+1)+1) s.val).finished=
          some (t.place (countedProgram countTape c.code).size) ∧
      cost≤(n+1)*(13*xs.length+15)+n*(c.steps*operationCost B+1) ∧
      Ready S (iterateControl c v n) t := by
  obtain ⟨cost,t,_,he,hb,_,_,hcost⟩ :=
    controlCounted_executes S countTape hc c hv n B v hw hg ha input tape xs origin s hn hcount hs
  obtain ⟨hrun,_⟩ := he.compiled_run ((n+1)*(13*xs.length+15)+n*(c.steps*operationCost B+1)+1) (by omega)
  exact ⟨cost,t,hrun,hcost,hb⟩

#print axioms controlCounted_computes

end Maxwell.Continuum.RationalDataflow
