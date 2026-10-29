import Maxwell.Cost.PositiveGraph.Metadata.Plan
import Maxwell.Cost.PositiveGraph.Metadata.Dimension

namespace Maxwell.Cost.PositiveGraph.Metadata
open Structured
open RationalAccumulator (Word Blank word_of_eq blank_of_eq)

def work : Finset ℕ := {0,1,2,3} ∪ Finset.Icc 140 159
def code : Code := .seq dimensionCode (.seq numericCode clockCode)
def price (width dimension count : ℕ) : ℕ := numericPrice width dimension count+55*width+93

theorem Numeric.transport {width dimension count : ℕ} {s t : BitRAMState}
    (h : Numeric width dimension count s)
    (keep : ∀ i, 140 ≤ i → i ≤ 159 → i ≠ 146 → t.tapes i=s.tapes i) :
    Numeric width dimension count t := by
  exact ⟨word_of_eq (keep 140 (by omega) (by omega) (by omega)) h.widthWord,
    word_of_eq (keep 141 (by omega) (by omega) (by omega)) h.vertices,
    word_of_eq (keep 142 (by omega) (by omega) (by omega)) h.incidences,
    word_of_eq (keep 143 (by omega) (by omega) (by omega)) h.counterBase,
    word_of_eq (keep 144 (by omega) (by omega) (by omega)) h.rankBase,
    word_of_eq (keep 145 (by omega) (by omega) (by omega)) h.diagonalBase,
    word_of_eq (keep 147 (by omega) (by omega) (by omega)) h.four,
    word_of_eq (keep 148 (by omega) (by omega) (by omega)) h.clockFour,
    word_of_eq (keep 149 (by omega) (by omega) (by omega)) h.two,
    word_of_eq (keep 150 (by omega) (by omega) (by omega)) h.clockTwo,
    word_of_eq (keep 151 (by omega) (by omega) (by omega)) h.endpointBase,
    word_of_eq (keep 153 (by omega) (by omega) (by omega)) h.edges,
    word_of_eq (keep 154 (by omega) (by omega) (by omega)) h.doubledDimension,
    fun i hi hj => blank_of_eq (keep i (by omega) hj (by omega)) (h.temporary i hi hj)⟩

set_option maxRecDepth 16384 in
/-- All graph metadata is generated from the actual source compiler's
identifier, measured width and counted sparse entries. No array descriptor
is supplied as additional machine input. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (width d count : ℕ)
    (hd : d < 2^width) (clockBits : List Bool) (hclockLength : clockBits.length=width)
    (s : Store) (h90 : Word s.val 90 width)
    (h95 : BankArray.Word s.val 95 (SourceCircuit.fixedWidth width d))
    (h93 : BankArray.Word s.val 93 clockBits) (h116 : Word s.val 116 count)
    (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (fresh : ∀ i, 140 ≤ i → i ≤ 159 → Blank s.val i) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ price width d count ∧
      Numeric width d count t.val ∧
      (∃ bits, bits.length=width+3 ∧ BankArray.Word t.val 146 bits) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨dcost,a,ea,hda,ad,fa⟩ := dimension input tape width d hd s h95 (fresh 154 (by omega) (by omega))
  have bank : NatAssign.Bank ids (initial width d count) a.val := by
    intro i hi
    simp only [ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
    rcases hi with (rfl | rfl) | ⟨hlo,hhi⟩
    · simpa [initial] using word_of_eq (fa.tapes 90 (by decide)) h90
    · simpa [initial] using word_of_eq (fa.tapes 116 (by decide)) h116
    · by_cases he : i=154
      · subst i; simpa [initial] using ad
      · have zero : Word a.val i 0 := (RationalAccumulator.zero_word_iff_blank _ _).mpr
          (blank_of_eq (fa.tapes i (by simpa using he)) (fresh i hlo hhi))
        simpa [initial,he,show i≠90 by omega,show i≠116 by omega] using zero
  have small : NatAssign.Scratch s.val := by
    intro i hi
    interval_cases i
    · exact hs.1
    · exact hs.2.1
    · exact hs.2.2.1
    · exact hs.2.2.2.1
  have asmall : NatAssign.Scratch a.val := fun i hi =>
    blank_of_eq (fa.tapes i (by simp; omega)) (small i hi)
  obtain ⟨ncost,b,eb,hnb,bb,bs,fb⟩ := NatAssign.executes ids ids_lower statements valid
    (initial width d count) input tape a bank asmall
  have faw : BinaryPrecision.Frame work s.val a.val := fa.mono (by simp [work])
  have fbw : BinaryPrecision.Frame work a.val b.val := fb.mono (by decide)
  have fab := faw.trans fbw
  have numeric := numeric_of_bank width d count b.val bb
  have b146 : Blank b.val 146 := by
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa [NatAssign.values,statements,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial] using bb 146 (by simp [ids])
  obtain ⟨clockOrigin,hco⟩ := h93
  obtain ⟨t,et,hclock,ft⟩ := clock input tape clockBits clockOrigin b
    ((fab.tapes 93 (by decide)).trans hco) b146
  have ftw : BinaryPrecision.Frame work b.val t.val := ft.mono (by simp [work])
  have frame := fab.trans ftw
  have ts : NatAssign.Scratch t.val := fun i hi =>
    blank_of_eq (ft.tapes i (by simp; omega)) (bs i hi)
  refine ⟨dcost+(ncost+(24*clockBits.length+58)),t,ea.seq (eb.seq et),?_,
    numeric.transport (fun i _ _ hi => ft.tapes i (by simpa using hi)),
    ⟨clockBits++[false,false,false],by simp [hclockLength],hclock⟩,
    ⟨ts 0 (by decide),ts 1 (by decide),ts 2 (by decide),ts 3 (by decide),
      blank_of_eq (frame.tapes 5 (by decide)) hs.2.2.2.2.1,
      blank_of_eq (frame.tapes 6 (by decide)) hs.2.2.2.2.2.1,
      blank_of_eq (frame.tapes 8 (by decide)) hs.2.2.2.2.2.2.1,
      blank_of_eq (frame.tapes 9 (by decide)) hs.2.2.2.2.2.2.2⟩,
    blank_of_eq (frame.tapes 7 (by decide)) h7,
    blank_of_eq (frame.tapes 37 (by decide)) h37,frame⟩
  dsimp [price,numericPrice]
  rw [hclockLength]
  omega

def program : BitRAM := code.compile

end Maxwell.Cost.PositiveGraph.Metadata
