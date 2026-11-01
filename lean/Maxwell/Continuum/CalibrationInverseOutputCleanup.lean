import Maxwell.Continuum.CalibrationInverseOutputGather
import Maxwell.Cost.Structured.WordCleanup

/-! Once all inverse entries have been gathered, retire the actual array
readout scratch and recover the rational arithmetic Ready contract. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine.OutputCleanup
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix RationalDataflow
set_option maxHeartbeats 3000000

def coldWords : List ℕ := [33,34,35,36,102,103,104,105,106]
def clearWords : List ℕ := [100,101,102,103,104,105,106,30,31,32,33,34,35,36]
def code : Code := WordCleanup.code clearWords
def costBound (B : ℕ) : ℕ := 14*(6*B+4)+1

theorem cold_mem (k : ℕ) : k∈coldWords↔k∈OutputPoint.coldIds := by
  simp [coldWords,OutputPoint.coldIds]

theorem cold_bounded {n B : ℕ} (a : Snapshot n) (count : List Bool) (s : BitRAMState)
    (ready:a.Ready count B s) (blank105:RationalAccumulator.Blank s 105) :
    WordCleanup.Bounded coldWords B s := by
  obtain ⟨vi,_,hlen,old,indices,index104,_,blank106,_,_,_⟩:=ready.1
  have zeros (k : ℕ) (lo:33≤k) (hi:k≤36) : RationalAccumulator.Word s k 0 := by
    simpa only [dotValues,Function.update_apply,ite_self] using old.1 k (by omega) hi
  intro k hk
  simp only [coldWords,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨[],by simp,zeros 33 (by decide) (by decide)⟩
  · exact ⟨[],by simp,zeros 34 (by decide) (by decide)⟩
  · exact ⟨[],by simp,zeros 35 (by decide) (by decide)⟩
  · exact ⟨[],by simp,zeros 36 (by decide) (by decide)⟩
  · exact ⟨[],by simp,indices.1⟩
  · exact ⟨vi,hlen,indices.2⟩
  · exact ⟨[],by simp,index104⟩
  · exact ⟨[],by simp,(RationalAccumulator.zero_word_iff_blank _ _).mpr blank105⟩
  · exact ⟨[],by simp,(RationalAccumulator.zero_word_iff_blank _ _).mpr blank106⟩

theorem cold_transfer {B : ℕ} {s t : BitRAMState}
    (h:WordCleanup.Bounded coldWords B s)
    (keep:∀k∈OutputPoint.coldIds,t.tapes k=s.tapes k) : WordCleanup.Bounded coldWords B t := by
  intro k hk
  obtain ⟨bits,width,word⟩:=h k hk
  exact ⟨bits,width,BankArray.word_of_eq (keep k ((cold_mem k).mp hk)) word⟩

theorem cold_prepare {B : ℕ} {s t : BitRAMState}
    (h:WordCleanup.Bounded coldWords B s)
    (frame:BinaryPrecision.Frame DenominatorPower.changed s t) : WordCleanup.Bounded coldWords B t := by
  apply cold_transfer h
  intro k hk
  simp only [OutputPoint.coldIds,Finset.mem_insert,Finset.mem_singleton] at hk
  apply frame.tapes
  simp only [DenominatorPower.changed,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem executes {n D : ℕ} (a : Snapshot n) (S : Finset ℕ) (p : ℕ→Parts) (v : ℕ→ℕ)
    (B : ℕ) (size:a.data.Sized B) (width:∀k∈OutputRead.ids,(v k).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state:OutputPoint.State a D v s.val) (cold:WordCleanup.Bounded coldWords B s.val)
    (cells:Cells S p s.val) :
    ∃cost t, Executes input tape code cost s t ∧ cost≤costBound B ∧
      Ready S p t ∧ BinaryPrecision.Frame clearWords.toFinset s.val t.val := by
  have words:WordCleanup.Bounded clearWords B s.val:=by
    intro k hk
    by_cases h100:k=100
    · subst k;exact ⟨a.data.width,size.1,state.stored.width⟩
    by_cases h101:k=101
    · subst k;exact ⟨a.data.clock,by rw [a.data.clock_length];exact size.2.1,state.stored.clock⟩
    by_cases hread:k∈OutputRead.ids
    · exact ⟨(v k).bits,width k hread,state.bank k hread⟩
    apply cold k
    simp only [clearWords,List.mem_cons,List.not_mem_nil,or_false] at hk
    simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton] at hread
    simp only [coldWords,List.mem_cons,List.not_mem_nil,or_false]
    omega
  obtain ⟨cost,t,executes,bound,blank,frame⟩:=WordCleanup.executes clearWords B input tape s words
  have cells':Cells S p t.val:=cells.transfer (by
    intro k hk
    apply frame.tapes
    simp only [List.mem_toFinset,clearWords,List.mem_cons,List.not_mem_nil,or_false]
    omega)
  have scratch:NatAssign.Scratch t.val:=by
    intro k hk
    have keep:t.val.tapes k=s.val.tapes k:=frame.tapes k (by
      simp only [List.mem_toFinset,clearWords,List.mem_cons,List.not_mem_nil,or_false]
      omega)
    apply RationalAccumulator.blank_of_eq keep
    interval_cases k
    · exact state.scratch.1
    · exact state.scratch.2.1
    · exact state.scratch.2.2.1
    · exact state.scratch.2.2.2.1
  refine ⟨cost,t,executes,bound,cells'.ready ?_ scratch,frame⟩
  intro k hk
  apply blank k
  simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton] at hk
  simpa only [clearWords,List.mem_cons,List.not_mem_nil,or_false,or_assoc] using hk

#print axioms executes
end Maxwell.Continuum.Calibration.NeumannMachine.OutputCleanup
