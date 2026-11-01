import Maxwell.Continuum.CalibrationInverseEntryRead

/-! Turn the completed integer inverse into a reusable rational readout.
Its denominator power is computed from the stored denominator and countdown;
the numerator accumulators are already zero in the inverse's WorkReady state. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine.OutputPrepare
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def numbers (D N : ℕ) (work : ℕ→ℕ) (k : ℕ) : ℕ :=
  if k=126 then D else if k=304 then N else work k
def width (D N C : ℕ) : ℕ := D.bits.length+N.bits.length+C+1
def code : Code := DenominatorPower.code
def indexIds : Finset ℕ := {140,304,530,531,533,534}
def indexNumbers (D N k : ℕ) : ℕ :=
  if k=304 then N else if k=530 then D else if k=531 ∨ k=533 then 1 else 0

structure Ready {n : ℕ} (a : Snapshot n) (D : ℕ) (s : BitRAMState) : Prop where
  stored : Horner.Stored a.data a.words s
  ports : Horner.Ports a.data 10 11 5 4 s
  scratch : BankArray.Scratch s
  seven : RationalAccumulator.Blank s 7
  bank : NatAssign.Bank OutputRead.ids (fun _=>0) s
  denominator : RationalAccumulator.Word s 532 D
  index : RationalAccumulator.Blank s 140

theorem executes {n : ℕ} (a : Snapshot n) (count : List Bool) (B D N C : ℕ) (work : ℕ→ℕ)
    (hw : ∀k∈Finset.Icc 530 534,(work k).bits.length≤C)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (ready : a.Ready count B s.val)
    (denominator : RationalAccumulator.Word s.val 126 D)
    (counter : RationalAccumulator.Word s.val 304 N)
    (working : NatAssign.Bank (Finset.Icc 530 534) work s.val)
    (index : RationalAccumulator.Blank s.val 140) :
    ∃cost t, Executes input tape code cost s t ∧
      cost≤DenominatorPower.costBound N (width D N C) ∧ Ready a (D^(N+1)) t.val ∧
      NatAssign.Bank indexIds (indexNumbers D N) t.val ∧
      BinaryPrecision.Frame DenominatorPower.changed s.val t.val := by
  have each (k : ℕ) (hk:k∈DenominatorPower.ids) :
      RationalAccumulator.Word s.val k (numbers D N work k) ∧
        (numbers D N work k).bits.length≤width D N C := by
    unfold numbers
    split_ifs with hD hN
    · subst k;exact ⟨denominator,by unfold width;omega⟩
    · subst k;exact ⟨counter,by unfold width;omega⟩
    · have hc:k∈Finset.Icc 530 534:=by
        simp only [DenominatorPower.ids,Finset.mem_insert,Finset.mem_singleton] at hk
        simp only [Finset.mem_Icc]
        omega
      exact ⟨working k hc,by have h:=hw k hc;unfold width;omega⟩
  obtain ⟨vi,_,_,old,_,_,_,_,_,_,_⟩:=ready.1
  have scratch : NatAssign.Scratch s.val := by
    intro k hk
    interval_cases k
    · exact old.2.1.1
    · exact old.2.1.2.1
    · exact old.2.1.2.2.1
    · exact old.2.1.2.2.2.1
  obtain ⟨cost,t,executes,bound,power,one,base,unit,temp,zero,frame⟩:=
    DenominatorPower.executes (numbers D N work) (width D N C) (by unfold width;omega)
      (fun k hk=>(each k hk).2) input tape s (fun k hk=>(each k hk).1) scratch
  have keep (k : ℕ) (hk:4≤k) (hout:k<530 ∨ 534<k) : t.val.tapes k=s.val.tapes k := by
    apply frame.tapes
    simp only [DenominatorPower.changed,Finset.mem_insert,Finset.mem_singleton]
    omega
  have fullScratch : BankArray.Scratch t.val :=
    ⟨zero 0 (by decide),zero 1 (by decide),zero 2 (by decide),zero 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by decide) (by omega)) old.2.1.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by decide) (by omega)) old.2.1.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by decide) (by omega)) old.2.1.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by decide) (by omega)) old.2.1.2.2.2.2.2.2.2⟩
  have bank : NatAssign.Bank OutputRead.ids (fun _=>0) t.val := by
    intro k hk
    have bounds:30≤k ∧ k≤32:=by
      simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    have word:=old.1 k bounds.1 (by omega)
    have zeros:dotValues 0 0 k=0:=by simp only [dotValues,Function.update_apply,ite_self]
    apply RationalAccumulator.word_of_eq (keep k (by omega) (by omega))
    simpa only [zeros] using word
  refine ⟨cost,t,executes,?_,⟨DenominatorPower.stored_preserved a ready.2.1 frame,?_,fullScratch,
    RationalAccumulator.blank_of_eq (keep 7 (by decide) (by omega)) old.2.2,bank,?_,
    RationalAccumulator.blank_of_eq (keep 140 (by decide) (by omega)) index⟩,?_,frame⟩
  · simpa [numbers] using bound
  · exact ⟨BankArray.word_of_eq (keep 112 (by decide) (by omega)) ready.2.2.inputPositive,
      BankArray.word_of_eq (keep 113 (by decide) (by omega)) ready.2.2.inputNegative,
      BankArray.word_of_eq (keep 114 (by decide) (by omega)) ready.2.2.outputPositive,
      BankArray.word_of_eq (keep 115 (by decide) (by omega)) ready.2.2.outputNegative⟩
  · simpa [numbers] using power
  · intro k hk
    simp only [indexIds,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [indexNumbers,RationalAccumulator.zero_word_iff_blank] using
        RationalAccumulator.blank_of_eq (keep 140 (by decide) (by omega)) index
    · simpa [indexNumbers] using RationalAccumulator.word_of_eq (keep 304 (by decide) (by omega)) counter
    · simpa [indexNumbers,numbers] using base
    · simpa [indexNumbers] using unit
    · simpa [indexNumbers] using one
    · simpa [indexNumbers,RationalAccumulator.zero_word_iff_blank] using temp

#print axioms executes
end Maxwell.Continuum.Calibration.NeumannMachine.OutputPrepare
