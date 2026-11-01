import Maxwell.Continuum.StoredDecoderDescription
import Maxwell.Cost.Structured.StoredPowerOfTwo

/-! The final decoder bank is installed from actual retained selector words,
geometry words, and the current raw numerator. Its temporary words are
cleared by scans, and its dyadic denominator is regenerated from tape 990. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def selectorPorts : Finset ℕ:={4705,4706,4707,4708}
def initializeCode : Code:=.seq (WordCleanup.code outputList) (StoredPowerOfTwo.code 990 4800 144)
def initializeWork : Finset ℕ:=outputs∪{144}
def initialValues (gv nv : ℕ→ℕ) (rv : ℕ→Parts) (P i : ℕ) : ℕ:=
  if i∈outputs then 0 else if i=144 then 2^P else if i=1000 then (rv 0).positive else
  if i∈selectorPorts then nv i else gv i
def initializeCost (P H : ℕ) : ℕ:=8*(6*H+4)+1+
  (2*(6*H+4)+1+((P+1)*(13*P.bits.length+25)+21*P.bits.length+27))

theorem initialize_executes {n J base slotWidth G B : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv nv : ℕ→ℕ} {rv : ℕ→Parts} {table : Table J} {s : Store}
    (g : GeometryOutput.Context data base slotWidth G clock constants gv s)
    (array : table.Ready s) (raw : RationalDataflow.Ready StoredInteger.slots rv s)
    (rawWidth : WidthBank StoredInteger.slots B rv) (geometryWidth : G≤B)
    (selectors : NatAssign.Bank selectorPorts nv s.val)
    (selectorWidth : ∀i∈selectorPorts,(nv i).bits.length≤B)
    (P H : ℕ) (powerWidth : (2^P).bits.length≤B) (precision : Word s.val 990 P)
    (old : WordCleanup.Bounded outputList H s.val)
    (oldPower : List Bool) (oldPowerWidth : oldPower.length≤H) (power : BankArray.Word s.val 144 oldPower)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape initializeCode cost s t ∧cost ≤ initializeCost P H ∧
      GeometryOutput.Context data base slotWidth G clock constants gv t ∧table.Ready t ∧
      RationalDataflow.Ready StoredInteger.slots rv t ∧
      NatAssign.Bank ids (initialValues gv nv rv P) t.val ∧
      (∀i∈ids,(initialValues gv nv rv P i).bits.length≤B) ∧
      BinaryPrecision.Frame initializeWork s.val t.val:=by
  obtain ⟨c0,a,e0,hc0,blank0,f0⟩:=WordCleanup.executes outputList H input tape s old
  have oldA : WordCleanup.Bounded [4800,144] H a.val:=by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (blank0 4800 (by decide))⟩
    · exact ⟨oldPower,oldPowerWidth,BankArray.word_of_eq (f0.tapes 144 (by decide)) power⟩
  obtain ⟨c1,t,e1,hc1,powerT,temporary,f1⟩:=StoredPowerOfTwo.executes 990 4800 144
    (by decide) (by decide) (by decide) P H input tape a
    (word_of_eq (f0.tapes 990 (by decide)) precision) oldA
  have frame : BinaryPrecision.Frame initializeWork s.val t.val:=
    (f0.mono (by decide)).trans (f1.mono (by decide))
  have scratch : BankArray.Scratch t.val:=g.ready.scratch.of_tapes (fun i hi=>frame.tapes i (by
    simp only [initializeWork,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or];omega))
  have seven : Blank t.val 7:=blank_of_eq (frame.tapes 7 (by decide)) g.ready.seven
  have geometryT : GeometryOutput.Context data base slotWidth G clock constants gv t:=by
    apply g.storage_frame frame.memory _ (frame.tapes 962 (by decide)) scratch seven
    intro i hi
    exact frame.tapes i (fun hh=>Finset.disjoint_left.mp (by decide :
      Disjoint GeometryOutput.ids initializeWork) hi hh)
  have rawT : RationalDataflow.Ready StoredInteger.slots rv t:=by
    refine ⟨?_,?_⟩
    · intro i hi
      exact word_of_eq (frame.tapes i (fun hh=>Finset.disjoint_left.mp (by decide :
        Disjoint (RationalDataflow.ids StoredInteger.slots) initializeWork) hi hh)) (raw.1 i hi)
    · intro i hi
      exact blank_of_eq (frame.tapes i (by
        simp only [initializeWork,outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or];omega)) (raw.2 i hi)
  have cleared (i : ℕ) (hi : i∈outputs) : Blank t.val i:=by
    by_cases htemp:i=4800
    · subst i;exact temporary
    · apply blank_of_eq (f1.tapes i ?_) (blank0 i (by simpa [outputList,outputs] using hi))
      have h144 : i≠144:=by intro he;subst i;exact (by decide : 144∉outputs) hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨htemp,h144⟩
  have input_cases (i : ℕ) (hi : i∈ids) (ho : i∉outputs) (hp : i≠144) (hr : i≠1000)
      (hs : i∉selectorPorts) : i∈GeometryOutput.ids:=by
    simp only [ids,inputs,outputs,selectorPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ho hs
    simp only [GeometryOutput.ids,Finset.mem_erase,Finset.mem_Icc]
    omega
  have bankT : NatAssign.Bank ids (initialValues gv nv rv P) t.val:=by
    intro i hi
    by_cases ho:i∈outputs
    · simp only [initialValues,ite_eq_left ho]
      exact (zero_word_iff_blank _ _).mpr (cleared i ho)
    rw [initialValues,ite_eq_right ho]
    by_cases hp:i=144
    · subst i;simp only [ite_true];exact powerT
    rw [ite_eq_right hp]
    by_cases hr:i=1000
    · subst i;simp only [ite_true]
      simpa only [show (1000:ℕ)=positivePort 0 from rfl,dataValues_positive] using
        rawT.1 1000 (by decide)
    rw [ite_eq_right hr]
    by_cases hs:i∈selectorPorts
    · rw [ite_eq_left hs]
      exact word_of_eq (frame.tapes i (fun hh=>Finset.disjoint_left.mp (by decide :
        Disjoint selectorPorts initializeWork) hs hh)) (selectors i hs)
    · rw [ite_eq_right hs]
      exact geometryT.ready.bank i (input_cases i hi ho hp hr hs)
  refine ⟨c0+c1,t,e0.seq e1,?_,geometryT,?_,rawT,bankT,?_,frame⟩
  · change c0≤8*(6*H+4)+1 at hc0
    unfold initializeCost
    omega
  · apply array.storage_frame frame.memory _ scratch seven
    intro i hi
    exact frame.tapes i (fun hh=>Finset.disjoint_left.mp (by decide :
      Disjoint ({200,202,203,204,205}:Finset ℕ) initializeWork) hi hh)
  · intro i hi
    by_cases ho:i∈outputs
    · simp [initialValues,ho]
    rw [initialValues,ite_eq_right ho]
    by_cases hp:i=144
    · subst i;simp only [ite_true];exact powerWidth
    rw [ite_eq_right hp]
    by_cases hr:i=1000
    · subst i;simp only [ite_true];exact (rawWidth 0 (by decide)).1
    rw [ite_eq_right hr]
    by_cases hs:i∈selectorPorts
    · rw [ite_eq_left hs];exact selectorWidth i hs
    · rw [ite_eq_right hs]
      exact (g.wordWidth i (input_cases i hi ho hp hr hs)).trans geometryWidth

#print axioms initialize_executes
end Maxwell.Continuum.DecoderRow
