import Maxwell.Continuum.ContinuumDecoderSelectorData
import Maxwell.Cost.Structured.WordCleanup

/-! Install decoder metadata from retained input words. Old output words are
cleared by charged scans before the fixed arithmetic and ceiling-log code. -/
namespace Maxwell.Continuum.DecoderSelectors
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def outputList : List ℕ := [4700,4701,4702,4703,4704,4705,4706,4707,4708,4710,4712,4713,4714]
def initial (v : ℕ→ℕ) (i : ℕ) : ℕ := if i∈outputs then 0 else v i
def initializeCode : Code := .seq (WordCleanup.code outputList) code
def initializeCost (B H : ℕ) := 13*(6*H+4)+1+costBound B

theorem initial_inputs (v : ℕ→ℕ) (i : ℕ) (hi : i∈inputs) : initial v i=v i := by
  apply ite_eq_right
  exact fun ho => Finset.disjoint_left.mp (by decide : Disjoint inputs outputs) hi ho

theorem Inputs.initial {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
    {v : ℕ→ℕ} (h : Inputs p S hm v) : Inputs p S hm (initial v) := by
  constructor
  · simpa only [initial_inputs v 501 (by decide)] using h.nonzeros
  · simpa only [initial_inputs v 2245 (by decide)] using h.spectral
  · simpa only [initial_inputs v 2237 (by decide)] using h.radius_eq
  · simpa only [initial_inputs v 2221 (by decide)] using h.length_eq
  · simpa only [initial_inputs v 2244 (by decide)] using h.buffer_eq
  · intro j
    have hj : 2240+j.val∈inputs := by fin_cases j <;> decide
    simpa only [initial_inputs v _ hj] using h.span j
  · simpa only [initial_inputs v 4428 (by decide)] using h.moment
  · simpa only [initial_inputs v 506 (by decide),initial_inputs v 507 (by decide)] using h.sourceScale
  · simpa only [initial_inputs v 504 (by decide),initial_inputs v 505 (by decide)] using h.matrixScale

theorem result_outside (v : ℕ→ℕ) (i : ℕ) (hi : i∉outputs) : result v i=v i := by
  have h0 : i≠4701 := fun he => hi (he ▸ (by decide : 4701∈outputs))
  have h1 : i≠4710 := fun he => hi (he ▸ (by decide : 4710∈outputs))
  rw [result_kept v i h0 h1]
  apply NatAssign.values_preserves
  intro a ha he
  have target : a.target∈outputs := by
    simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact hi (he ▸ target)

theorem initialize_executes (v : ℕ→ℕ) (B H : ℕ) (hB : 10≤B)
    (width : ∀i∈inputs,(v i).bits.length≤B)
    (hm : 0<v 501) (hN : 0<v 2245) (htau : 0<v 2237)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank inputs v s.val) (scratch : NatAssign.Scratch s.val)
    (old : WordCleanup.Bounded outputList H s.val) :
    ∃cost t,Executes input tape initializeCode cost s t ∧cost ≤ initializeCost B H ∧
      NatAssign.Bank ids (result (initial v)) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(result (initial v) i).bits.length≤2*(arithmeticWidth B+1)) ∧
      BinaryPrecision.Frame ({0,1,2,3}∪outputs) s.val t.val := by
  obtain ⟨c,a,e,hc,blank,frame⟩ := WordCleanup.executes outputList H input tape s old
  have words : NatAssign.Bank ids (initial v) a.val := by
    intro i hi
    by_cases ho : i∈outputs
    · rw [initial,ite_eq_left ho]
      exact (zero_word_iff_blank _ _).mpr (blank i (by simpa [outputList,outputs] using ho))
    · have hin : i∈inputs := (Finset.mem_union.mp hi).resolve_right ho
      rw [initial_inputs v i hin]
      exact word_of_eq (frame.tapes i (by simpa [outputList,outputs] using ho)) (bank i hin)
  have widths : ∀i∈ids,(initial v i).bits.length≤B := by
    intro i hi
    by_cases ho : i∈outputs
    · simp [initial,ho]
    · rw [initial,ite_eq_right ho]
      exact width i ((Finset.mem_union.mp hi).resolve_right ho)
  have scratchA : NatAssign.Scratch a.val := by
    intro i hi
    apply blank_of_eq (frame.tapes i ?_) (scratch i hi)
    simp only [outputList,List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,Finset.notMem_empty,or_false]
    omega
  obtain ⟨d,t,et,hd,bt,st,wt,ft⟩ := executes (initial v) B hB widths
    (by simpa only [initial_inputs v 501 (by decide)] using hm)
    (by simpa only [initial_inputs v 2245 (by decide)] using hN)
    (by simpa only [initial_inputs v 2237 (by decide)] using htau) input tape a words scratchA
  exact ⟨c+d,t,e.seq et,Nat.add_le_add hc hd,bt,st,wt,(frame.mono (by decide)).trans ft⟩

#print axioms initialize_executes
#print axioms Inputs.initial
end Maxwell.Continuum.DecoderSelectors
