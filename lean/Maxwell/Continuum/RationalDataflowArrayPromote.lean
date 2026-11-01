import Maxwell.Continuum.RationalDataflowArrayOutputFrame
import Maxwell.Continuum.RationalDataflowArrayCost
import Maxwell.Cost.Structured.WordCleanup
import Maxwell.Cost.Structured.WordCopyPlan

/-! An actual output table becomes an input table by copying its five headers.
The old input headers may contain arbitrary bounded words; no old input-table
invariant or memory representation is required. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray.Promote
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def headers : List ℕ := [200,202,203,204,205]
def changed : Finset ℕ := headers.toFinset
def allIds : Finset ℕ := changed∪{210,212,213,214,215}
def plan : List (ℕ×ℕ) := [(210,200),(212,202),(213,203),(214,204),(215,205)]
def code : Code := .seq (WordCleanup.code headers) (WordCopyPlan.code plan)
def initial {n : ℕ} (a : Table n) (k : ℕ) : List Bool :=
  if k=210 then a.width else if k=212 then a.basePositive else if k=213 then a.baseNegative
  else if k=214 then a.baseDenominator else if k=215 then a.clock else []

theorem outputs {n : ℕ} (a : Table n) :
    WordCopyPlan.evaluate plan (initial a) 200=a.width ∧
    WordCopyPlan.evaluate plan (initial a) 202=a.basePositive ∧
    WordCopyPlan.evaluate plan (initial a) 203=a.baseNegative ∧
    WordCopyPlan.evaluate plan (initial a) 204=a.baseDenominator ∧
    WordCopyPlan.evaluate plan (initial a) 205=a.clock := by
  simp [plan,initial,WordCopyPlan.evaluate]

theorem scratch_frame {s t : BitRAMState} (h : BankArray.Scratch s)
    (f : BinaryPrecision.Frame changed s t) : BankArray.Scratch t := by
  rcases h with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
  exact ⟨RationalAccumulator.blank_of_eq (f.tapes 0 (by decide)) h0,
    RationalAccumulator.blank_of_eq (f.tapes 1 (by decide)) h1,
    RationalAccumulator.blank_of_eq (f.tapes 2 (by decide)) h2,
    RationalAccumulator.blank_of_eq (f.tapes 3 (by decide)) h3,
    RationalAccumulator.blank_of_eq (f.tapes 5 (by decide)) h5,
    RationalAccumulator.blank_of_eq (f.tapes 6 (by decide)) h6,
    RationalAccumulator.blank_of_eq (f.tapes 8 (by decide)) h8,
    RationalAccumulator.blank_of_eq (f.tapes 9 (by decide)) h9⟩

theorem executes {n : ℕ} (a : Table n) (W H : ℕ) (hw : a.MetadataWidth W)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (ha : a.OutputReady s)
    (old : WordCleanup.Bounded headers H s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤256*(W+H+1) ∧
      a.Ready t ∧ a.OutputReady t ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,z0,f0⟩ := WordCleanup.executes headers H input tape s old
  have bank : WordCopyPlan.Bank allIds (initial a) u.val := by
    intro k hk
    simp only [allIds,changed,headers,Finset.mem_union,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with (rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl)
    · simpa [initial,BankArray.Word,RationalAccumulator.Word] using (RationalAccumulator.zero_word_iff_blank _ _).mpr (z0 200 (by simp [headers]))
    · simpa [initial,BankArray.Word,RationalAccumulator.Word] using (RationalAccumulator.zero_word_iff_blank _ _).mpr (z0 202 (by simp [headers]))
    · simpa [initial,BankArray.Word,RationalAccumulator.Word] using (RationalAccumulator.zero_word_iff_blank _ _).mpr (z0 203 (by simp [headers]))
    · simpa [initial,BankArray.Word,RationalAccumulator.Word] using (RationalAccumulator.zero_word_iff_blank _ _).mpr (z0 204 (by simp [headers]))
    · simpa [initial,BankArray.Word,RationalAccumulator.Word] using (RationalAccumulator.zero_word_iff_blank _ _).mpr (z0 205 (by simp [headers]))
    · simpa [initial] using BankArray.word_of_eq (f0.tapes 210 (by decide)) ha.width
    · simpa [initial] using BankArray.word_of_eq (f0.tapes 212 (by decide)) ha.basePositive
    · simpa [initial] using BankArray.word_of_eq (f0.tapes 213 (by decide)) ha.baseNegative
    · simpa [initial] using BankArray.word_of_eq (f0.tapes 214 (by decide)) ha.baseDenominator
    · simpa [initial] using BankArray.word_of_eq (f0.tapes 215 (by decide)) ha.clock
  have width : ∀k∈allIds,(initial a k).length≤W := by
    intro k hk
    simp only [allIds,changed,headers,Finset.mem_union,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with (rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl)
    all_goals (simp only [initial]; norm_num)
    all_goals first | exact Nat.zero_le _ | exact hw.width | exact hw.basePositive |
      exact hw.baseNegative | exact hw.baseDenominator | exact hw.clock
  obtain ⟨c1,t,e1,hc1,b1,_,f1⟩ := WordCopyPlan.executes allIds W plan (by decide) (initial a) width input tape u bank
  have frame : BinaryPrecision.Frame changed s.val t.val := f0.trans (f1.mono (by decide))
  have scratch := scratch_frame ha.scratch frame
  have seven := RationalAccumulator.blank_of_eq (frame.tapes 7 (by decide)) ha.seven
  have output : a.OutputReady t := ha.transfer frame.memory (by
    intro k hk
    apply frame.tapes k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    simp only [changed,headers,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    omega) scratch seven
  have result := outputs a
  have ready : a.Ready t := ⟨scratch,seven,by simpa only [result.1] using b1 200 (by decide),
    by simpa only [result.2.1] using b1 202 (by decide),
    by simpa only [result.2.2.1] using b1 203 (by decide),
    by simpa only [result.2.2.2.1] using b1 204 (by decide),
    by simpa only [result.2.2.2.2] using b1 205 (by decide),output.positive,output.negative,output.denominator⟩
  refine ⟨c0+c1,t,e0.seq e1,?_,ready,output,frame⟩
  norm_num only [headers,plan,List.length_cons,List.length_nil] at hc0 hc1
  omega

#print axioms executes
end Maxwell.Continuum.RationalDataflow.PartArray.Promote
