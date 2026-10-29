import Maxwell.Cost.DecoderTerm.Convert
import Maxwell.Cost.DecoderTerm.Weight
import Maxwell.Cost.DecoderTerm.Sign
import Maxwell.Cost.DecoderTerm.Value

/-! The general decoder term is an actual fixed finite program. Constants
66 and 67 are reusable, canonical center and denominator words; their actual
metadata-driven construction is separate from this per-sample operation. -/
namespace Maxwell.Cost.DecoderTerm
open Structured
open RationalAccumulator (Word Blank)

def code : Code := .seq (.call saveSign) (.seq convertCode (.seq weightCode (.call finishSign)))
def program : BitRAM := code.compile

def costBound (sample : List Bool) (center scale num den : ℕ) : ℕ :=
  5000*(sample.length+center.bits.length+num.bits.length+den.bits.length+scale.bits.length+4)^2

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 7 → i ≠ 12 → i ≠ 13 → i ≠ 33 → i ≠ 34 → i ≠ 65 →
    t.tapes i = s.tapes i) ∧
  t.registers 23 = s.registers 23 ∧
  (∀ i, 15 ≤ i → i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 35 → i ≠ 65 →
    t.registers i = s.registers i)

/-- All input words, including zero weight numerator and arbitrary padded
sample bits, are processed by the same compiled finite code. -/
theorem executes (input : List Bool) (randomTape : ℕ → Bool) (sample : List Bool)
    (sampleOrigin : ℤ) (center scale num den : ℕ) (s : Store)
    (h7 : s.val.tapes 7 = BitTape.shiftedEnd sample sampleOrigin)
    (h12 : s.val.tapes 12 = BitTape.atEnd num.bits)
    (h13 : s.val.tapes 13 = BitTape.atEnd den.bits)
    (h66 : Word s.val 66 center) (h67 : Word s.val 67 scale)
    (hblank : ∀ i, i < 4 → Blank s.val i)
    (h33 : Blank s.val 33) (h34 : Blank s.val 34) (h65 : Blank s.val 65) :
    ∃ cost, ∃ t : Store, cost ≤ costBound sample center scale num den ∧
      Executes input randomTape code cost s t ∧
      Word t.val 33 (magnitude sample center*num) ∧ Word t.val 34 (scale*den) ∧
      (∀ i, i < 4 → Blank t.val i) ∧ Blank t.val 7 ∧ Blank t.val 65 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧
      t.val.registers 35 = Bool.xor (SignedDifference.sign sample center.bits) (s.val.registers 23) ∧
      Frame s.val t.val := by
  let a := Store.ofState (saveState s.val)
  have ea := saveSign_steps input randomTape s
  obtain ⟨ccost,c,hccost,ec,hc65,hcblank,hc7,hc23,cf⟩ := convert input randomTape sample center
    sampleOrigin a h7 h66 hblank h65
  have ckeep (i : ℕ) (hi : 4 ≤ i) (h7' : i ≠ 7) (h65' : i ≠ 65) :
      c.val.tapes i = s.val.tapes i := cf.2.2.2.2.2.1 i hi h7' h65'
  obtain ⟨wcost,w,hwcost,ew,hw33,hw34,hwblank,hw65,hw12,hw13,wf⟩ :=
    weight input randomTape num den (magnitude sample center) scale c
      ((ckeep 12 (by omega) (by omega) (by omega)).trans h12)
      ((ckeep 13 (by omega) (by omega) (by omega)).trans h13) hc65
      (RationalAccumulator.word_of_eq (ckeep 67 (by omega) (by omega) (by omega)) h67) hcblank
      (RationalAccumulator.blank_of_eq (ckeep 33 (by omega) (by omega) (by omega)) h33)
      (RationalAccumulator.blank_of_eq (ckeep 34 (by omega) (by omega) (by omega)) h34)
  let t := Store.ofState (signState w.val)
  have ef := finishSign_steps input randomTape w
  have hw23 : w.val.registers 23 = SignedDifference.sign sample center.bits :=
    (wf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc23
  have hcSaved : c.val.registers 65 = s.val.registers 23 := by
    have hh := cf.2.2.2.2.2.2 65 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    simpa [a,Store.ofState,saveState] using hh
  have hwSaved : w.val.registers 65 = s.val.registers 23 :=
    (wf.2.2.2.2.2.2 65 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hcSaved
  refine ⟨_,t,?_,ea.seq (ec.seq (ew.seq ef)),hw33,hw34,hwblank,?_,hw65,hw12,hw13,?_,?_⟩
  · have hmag := magnitude_bits_le sample center
    let B := sample.length+center.bits.length+num.bits.length+den.bits.length+scale.bits.length+4
    have hwcap : wcost ≤ 2000*B^2 := hwcost.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [B]; omega) _))
    have hccap : ccost ≤ 500*B := by dsimp [B]; dsimp [magnitude] at hmag; omega
    have hB : B ≤ B^2 := by dsimp [B]; nlinarith
    change _ ≤ 5000*B^2
    have hb4 : 4 ≤ B := by dsimp [B]; omega
    nlinarith
  · exact RationalAccumulator.blank_of_eq
      (wf.2.2.2.2.2.1 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hc7
  · simp [t,Store.ofState,signState,hw23,hwSaved]
  · rcases cf with ⟨ca,ci,cm,cr,co,ct,cg⟩
    rcases wf with ⟨wa,wi,wm,wr,wo,wt,wg⟩
    refine ⟨wa.trans ca,wi.trans ci,wm.trans cm,wr.trans cr,wo.trans co,?_,?_,?_⟩
    · intro i hi h7' h12' h13' h33' h34' h65'
      exact (wt i hi h12' h13' h33' h34' h65').trans (ct i hi h7' h65')
    · simpa [t,Store.ofState,signState] using hwSaved
    · intro i hi h23 h24 h25 h26 h27 h35 h65'
      have hh := (wg i hi h24 h25 h26 h27).trans (cg i hi h23 h24 h25 h26 h27)
      simpa [t,Store.ofState,signState,a,saveState,h23,h35,h65'] using hh

theorem run (input : List Bool) (randomTape : ℕ → Bool) (sample : List Bool)
    (sampleOrigin : ℤ) (center scale num den : ℕ) (s : Store)
    (h7 : s.val.tapes 7 = BitTape.shiftedEnd sample sampleOrigin)
    (h12 : s.val.tapes 12 = BitTape.atEnd num.bits)
    (h13 : s.val.tapes 13 = BitTape.atEnd den.bits)
    (h66 : Word s.val 66 center) (h67 : Word s.val 67 scale)
    (hblank : ∀ i, i < 4 → Blank s.val i)
    (h33 : Blank s.val 33) (h34 : Blank s.val 34) (h65 : Blank s.val 65) :
    ∃ t : Store,
      (runPriced (program.next input randomTape) (costBound sample center scale num den+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (program.next input randomTape) (costBound sample center scale num den+1) s.val).instructions ≤
        costBound sample center scale num den ∧
      Word t.val 33 (magnitude sample center*num) ∧ Word t.val 34 (scale*den) ∧
      (∀ i, i < 4 → Blank t.val i) ∧ Blank t.val 7 ∧ Blank t.val 65 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧
      t.val.registers 35 = Bool.xor (SignedDifference.sign sample center.bits) (s.val.registers 23) ∧
      Frame s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := executes input randomTape sample sampleOrigin center scale num den s
    h7 h12 h13 h66 h67 hblank h33 h34 h65
  have hr := he.compiled_run (costBound sample center scale num den+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.DecoderTerm
