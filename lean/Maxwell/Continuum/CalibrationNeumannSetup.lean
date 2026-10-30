import Maxwell.Continuum.CalibrationNeumannStored

/-! Actual runtime setup after the coefficient-table copy. Descriptor
arithmetic and copying the width clock are both part of one fixed program.
No prepared inverse-loop state is assumed at the conclusion. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem Descriptors.Header.of_tapes {n w heap D N : ℕ} {s t : BitRAMState}
    (h : Descriptors.Header n w heap D N s)
    (hf : ∀ i, i≠101 → t.tapes i=s.tapes i) : Descriptors.Header n w heap D N t := by
  constructor
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.widthWord
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.dimension
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.denominator
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.numerator
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.iterations
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.matrixPositive
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.matrixNegative
  · intro i
    exact RationalAccumulator.word_of_eq (hf _ (by have := Horner.baseBank_bounds i; omega)) (h.bases i)
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.inputPositive
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.inputNegative
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.outputPositive
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.outputNegative
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.inputWidth
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.inputTablePositive
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.inputTableNegative
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.inputTableDenominator
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.outputWidth
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.outputTablePositive
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.outputTableNegative
  · exact RationalAccumulator.word_of_eq (hf _ (by decide)) h.outputTableDenominator
  · intro i hi hi'
    exact RationalAccumulator.word_of_eq (hf _ (by omega)) (h.accumulators i hi hi')
  · intro i hi
    have hne : i≠101 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
    exact RationalAccumulator.word_of_eq (hf _ hne) (h.cursors i hi)

def setupCode : Code := .seq Descriptors.code (WordReplace.code 205 101)
def setupCost (B width : ℕ) : ℕ := 3000*8^Descriptors.plan.length*(B+2)^2+15*width+21

theorem setup_executes {n : ℕ} (a b : PartArray.Table (tableSize n))
    (heap D N B : ℕ) (hw : 0<addressValue a.width) (hB : 0<B)
    (hl : TableLayout a b heap) (v : ℕ→ℕ)
    (hi : Descriptors.Inputs v n (addressValue a.width) heap D N)
    (hbits : ∀ i∈Descriptors.ids, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hbank : NatAssign.Bank Descriptors.ids v s.val)
    (ha : a.Ready s) (hb : b.OutputReady s) (h101 : RationalAccumulator.Blank s.val 101) :
    ∃ cost t, Executes input tape setupCode cost s t ∧
      cost≤setupCost B (addressValue a.width) ∧
      (initialSnapshot a b heap D hw s.val.memory).Ready n.bits B t.val ∧
      RationalAccumulator.Word t.val 140 N ∧ RationalAccumulator.Word t.val 304 N ∧
      t.val.memory=s.val.memory := by
  have scratch : NatAssign.Scratch s.val := by
    intro i hi
    interval_cases i
    · exact ha.scratch.1
    · exact ha.scratch.2.1
    · exact ha.scratch.2.2.1
    · exact ha.scratch.2.2.2.1
  obtain ⟨cost,u,eu,hcost,hu,hs,fu⟩ := Descriptors.executes v n (addressValue a.width)
    heap D N B hB hi hbits input tape s hbank scratch
  have keep (i : ℕ) (hi : i∈([5,6,7,8,9,37,101,205]:List ℕ)) : u.val.tapes i=s.val.tapes i := by
    apply fu.tapes
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [NatAssign.changes,Descriptors.plan,Descriptors.spanPlan,Descriptors.basesPlan,
        Descriptors.headerPlan,NatAssign.Instruction.target]
  have clock := BankArray.word_of_eq (keep 205 (by simp)) ha.clock
  have blank := RationalAccumulator.blank_of_eq (keep 101 (by simp)) h101
  obtain ⟨t,et,hclock,ft⟩ := WordReplace.executes 205 101 (by decide) input tape a.clock [] u
    clock ((RationalAccumulator.zero_word_iff_blank u.val 101).mpr blank)
  have htapes := ft.2.2.2.2.2.1
  have hheader := hu.of_tapes htapes
  have hz : BankArray.Scratch t.val := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact RationalAccumulator.blank_of_eq (htapes 0 (by decide)) (hs 0 (by decide))
    · exact RationalAccumulator.blank_of_eq (htapes 1 (by decide)) (hs 1 (by decide))
    · exact RationalAccumulator.blank_of_eq (htapes 2 (by decide)) (hs 2 (by decide))
    · exact RationalAccumulator.blank_of_eq (htapes 3 (by decide)) (hs 3 (by decide))
    · exact RationalAccumulator.blank_of_eq ((htapes 5 (by decide)).trans (keep 5 (by simp))) ha.scratch.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq ((htapes 6 (by decide)).trans (keep 6 (by simp))) ha.scratch.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq ((htapes 8 (by decide)).trans (keep 8 (by simp))) ha.scratch.2.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq ((htapes 9 (by decide)).trans (keep 9 (by simp))) ha.scratch.2.2.2.2.2.2.2
  have h7 := RationalAccumulator.blank_of_eq ((htapes 7 (by decide)).trans (keep 7 (by simp))) ha.seven
  have h37 := RationalAccumulator.blank_of_eq ((htapes 37 (by decide)).trans (keep 37 (by simp))) hb.packing
  have hm : t.val.memory=s.val.memory := ft.2.2.1.trans fu.memory
  have count304 : RationalAccumulator.Word t.val 304 N := by
    apply RationalAccumulator.word_of_eq
      ((htapes 304 (by decide)).trans (fu.tapes 304 (by decide)))
    simpa only [hi.iterations] using hbank 304 (by simp [Descriptors.ids])
  have hr := initial_ready (B := B) a b heap hw t.val hl hheader hclock hz h7 h37
    (by simpa only [hm] using ha.positive) (by simpa only [hm] using ha.negative)
    (by simpa only [hm] using hb.positive) (by simpa only [hm] using hb.negative)
  refine ⟨cost+(6*([].length)+15*a.clock.length+21),t,eu.seq et,?_,?_,hheader.iterations,count304,hm⟩
  · simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,a.clock_length,setupCost]
    omega
  · simpa only [hm] using hr

#print axioms setup_executes

end Maxwell.Continuum.Calibration.NeumannMachine
