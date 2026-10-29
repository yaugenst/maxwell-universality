import Maxwell.Cost.DecoderParser.Algebra
import Maxwell.Cost.RationalAccumulator.Reset

namespace Maxwell.Cost.DecoderParser
set_option maxRecDepth 4096
open Structured
open RationalAccumulator (Bank Scratch Word Blank bankValue)

/-- Each term reuses the same arithmetic program and erases its two temporary
operands after the rational accumulator has consumed them. -/
def accumulateCode : Code := .seq DecoderTerm.code
  (.seq RationalAccumulator.pushCode
    (.seq (.call (TapeOps.clear 33)) (.call (TapeOps.clear 34))))

def cleanTerm (v : ℕ → ℕ) : ℕ → ℕ := Function.update (Function.update v 33 0) 34 0

def ArithmeticFrame (s t : BitRAMState) : Prop :=
  t.address=s.address ∧ t.inputHead=s.inputHead ∧ t.memory=s.memory ∧
  t.randomCursor=s.randomCursor ∧ t.output=s.output ∧
  ∀ i, 4 ≤ i → i ≠ 7 → i ≠ 12 → i ≠ 13 → (i < 30 ∨ 36 < i) → i ≠ 65 → t.tapes i=s.tapes i

theorem ArithmeticFrame.trans {s t u : BitRAMState}
    (h : ArithmeticFrame s t) (k : ArithmeticFrame t u) : ArithmeticFrame s u := by
  rcases h with ⟨ha,hi,hm,hr,ho,ht⟩
  rcases k with ⟨ka,ki,km,kr,ko,kt⟩
  exact ⟨ka.trans ha,ki.trans hi,km.trans hm,kr.trans hr,ko.trans ho,
    fun i h4 h7 h12 h13 hb h65 =>  (kt i h4 h7 h12 h13 hb h65).trans (ht i h4 h7 h12 h13 hb h65)⟩

theorem ArithmeticFrame.of_term {s t : BitRAMState} (h : DecoderTerm.Frame s t) :
    ArithmeticFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i hi h7 h12 h13 hb h65 =>  h.2.2.2.2.2.1 i hi h7 h12 h13 (by omega) (by omega) h65⟩

theorem ArithmeticFrame.of_bank {s t : BitRAMState} (h : RationalAccumulator.Frame s t) :
    ArithmeticFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i hi _ _ _ hb _ =>  h.2.2.2.2.2.1 i hi hb⟩

def termWidth (F : Target.FixedPointFormat) (q : ℚ) (sample : List Bool) : ℕ :=
  sample.length+(2^(F.integerBits+F.fractionalBits)).bits.length+
    q.num.natAbs.bits.length+(2^F.fractionalBits).bits.length+q.den.bits.length+4

/-- The actual arithmetic endpoint for one parsed weight and fetched word.
The persistent bank represents the public decoder's exact rational update;
its width increases only by the fresh term's width. -/
theorem accumulate_steps (input : List Bool) (randomTape : ℕ → Bool)
    (F : Target.FixedPointFormat) (w : F.Word) (q : ℚ) (sample : List Bool)
    (hsample : addressValue sample=w.val) (sampleOrigin : ℤ) (v : ℕ → ℕ) (A : ℕ)
    (hd : 0 < v 32) (hv : Algebra.CoreShort A v)
    (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0) (s : Store)
    (h7 : s.val.tapes 7=BitTape.shiftedEnd sample sampleOrigin)
    (h12 : s.val.tapes 12=BitTape.atEnd q.num.natAbs.bits)
    (h13 : s.val.tapes 13=BitTape.atEnd q.den.bits)
    (hsign : s.val.registers 23=decide (q.num < 0))
    (h66 : Word s.val 66 (2^(F.integerBits+F.fractionalBits)))
    (h67 : Word s.val 67 (2^F.fractionalBits))
    (hb : Bank s.val v) (hr : Scratch s.val 0) (h65 : Blank s.val 65) :
    ∃ cost, ∃ t : Store, ∃ v' : ℕ → ℕ,
      cost  ≤  20000*(A+termWidth F q sample+2)^2 ∧
      Executes input randomTape accumulateCode cost s t ∧
      Bank t.val v' ∧ Scratch t.val 0 ∧
      bankValue v'=bankValue v+q*F.value w ∧
      0 < v' 32 ∧ Algebra.CoreShort (A+termWidth F q sample+1) v' ∧
      v' 33=0 ∧ v' 34=0 ∧ v' 35=0 ∧ v' 36=0 ∧
      Blank t.val 7 ∧ Blank t.val 65 ∧
      t.val.tapes 12=BitTape.blank ∧ t.val.tapes 13=BitTape.blank ∧
      ArithmeticFrame s.val t.val := by
  let B := termWidth F q sample
  let tv := DecoderTerm.termBank v
    (DecoderTerm.magnitude sample (2^(F.integerBits+F.fractionalBits))*q.num.natAbs)
    ((2^F.fractionalBits)*q.den)
  have ht33 : (tv 33).bits.length ≤ B := by
    have hm := DecoderTerm.magnitude_bits_le sample (2^(F.integerBits+F.fractionalBits))
    have hp := RationalAccumulator.bits_mul_le
      (DecoderTerm.magnitude sample (2^(F.integerBits+F.fractionalBits))) q.num.natAbs
    dsimp [tv,DecoderTerm.termBank,B,termWidth]
    simp only [Function.update_of_ne (by decide : (33:ℕ) ≠ 34),Function.update_self]
    omega
  have ht34 : (tv 34).bits.length ≤ B := by
    have hp := RationalAccumulator.bits_mul_le (2^F.fractionalBits) q.den
    dsimp [tv,DecoderTerm.termBank,B,termWidth]
    simp only [Function.update_self]
    omega
  have htbits : ∀ i,30 ≤ i → i ≤ 36 → (tv i).bits.length ≤ A+B := by
    intro i hi hi'
    interval_cases i  <;>  simp [tv,DecoderTerm.termBank,h35,h36]
    · exact hv.1.trans (Nat.le_add_right _ _)
    · exact hv.2.1.trans (Nat.le_add_right _ _)
    · exact hv.2.2.trans (Nat.le_add_right _ _)
    · exact ht33.trans (Nat.le_add_left _ _)
    · exact ht34.trans (Nat.le_add_left _ _)
  obtain ⟨c,a,hc,ea,hab,har,hvalue,htd,ha7,ha65,ha12,ha13,haf⟩ :=
    DecoderTerm.fixedPoint_executes input randomTape F w q sample hsample sampleOrigin v s
      h7 h12 h13 hsign h66 h67 hb h33 h34 hr h65
  have htd0 : 0 < tv 32 := by simpa [tv,DecoderTerm.termBank] using hd
  have htz : tv 36=0 := by simpa [tv,DecoderTerm.termBank] using h36
  obtain ⟨p,b,hp,eb,hbb,hbr,hbf⟩ := RationalAccumulator.push input randomTape tv (A+B)
    (a.val.registers 35) htbits htd0 htd htz a hab har rfl
  let pv := RationalAccumulator.pushed tv (a.val.registers 35)
  obtain ⟨cstate,ec,hcb,hcr,hcf⟩ := RationalAccumulator.clear_bank 33 (by decide) (by decide)
    input randomTape pv 0 b hbb hbr
  obtain ⟨t,et,htb,htr,htf⟩ := RationalAccumulator.clear_bank 34 (by decide) (by decide)
    input randomTape (Function.update pv 33 0) 0 cstate hcb hcr
  have htail := (hbf.trans hcf).trans htf
  have hp33 : pv 33=tv 33 := by cases hs : a.val.registers 35  <;>  simp [pv,RationalAccumulator.pushed,RationalAccumulator.prepared,RationalAccumulator.selected,hs]
  have hp34 : pv 34=tv 34 := by cases hs : a.val.registers 35  <;>  simp [pv,RationalAccumulator.pushed,RationalAccumulator.prepared,RationalAccumulator.selected,hs]
  have hp35 : pv 35=0 := by cases hs : a.val.registers 35  <;>  simp [pv,RationalAccumulator.pushed,RationalAccumulator.prepared,RationalAccumulator.selected,hs,tv,DecoderTerm.termBank,h35]
  have hp36 : pv 36=0 := by cases hs : a.val.registers 35  <;>  simp [pv,RationalAccumulator.pushed,RationalAccumulator.prepared,RationalAccumulator.selected,hs]
  have hpbits := Algebra.pushed_bits_linear tv (a.val.registers 35) A B
    (by simpa [Algebra.CoreShort,tv,DecoderTerm.termBank] using hv) ht33 ht34
    (by simp [tv,DecoderTerm.termBank,h35])
  refine ⟨c+(p+((6*(pv 33).bits.length+4)+(6*((Function.update pv 33 0) 34).bits.length+4))),
    t,cleanTerm pv,?_,ea.seq (eb.seq (ec.seq et)),htb,htr,?_,?_,?_,
    by simp [cleanTerm],by simp [cleanTerm],by simpa [cleanTerm] using hp35,
    by simpa [cleanTerm] using hp36,?_,?_,?_,?_,
    (ArithmeticFrame.of_term haf).trans (ArithmeticFrame.of_bank htail)⟩
  · have hc' : c ≤ 5000*B^2 := by simpa [DecoderTerm.costBound,B,termWidth,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hc
    have hclean : 6*(pv 33).bits.length+4+(6*((Function.update pv 33 0) 34).bits.length+4) ≤ 12*B+8 := by
      simp only [Function.update_of_ne (by decide : (34:ℕ) ≠ 33),hp33,hp34]
      omega
    change _ ≤ 20000*(A+B+2)^2
    nlinarith only [hc',hp,hclean,Nat.zero_le A,Nat.zero_le B]
  · have hval := RationalAccumulator.pushed_value tv (a.val.registers 35) htd0 htd
    rw [hvalue] at hval
    simpa [cleanTerm,bankValue,pv,tv,DecoderTerm.termBank] using hval
  · have hd' := RationalAccumulator.pushed_denominator_pos tv (a.val.registers 35) htd0 htd
    simpa [cleanTerm,pv] using hd'
  · exact ⟨by simpa [cleanTerm] using hpbits 30 (by decide) (by decide),
      by simpa [cleanTerm] using hpbits 31 (by decide) (by decide),
      by simpa [cleanTerm] using hpbits 32 (by decide) (by decide)⟩
  · exact RationalAccumulator.blank_of_eq (htail.2.2.2.2.2.1 7 (by decide) (Or.inl (by decide))) ha7
  · exact RationalAccumulator.blank_of_eq (htail.2.2.2.2.2.1 65 (by decide) (Or.inr (by decide))) ha65
  · exact (htail.2.2.2.2.2.1 12 (by decide) (Or.inl (by decide))).trans ha12
  · exact (htail.2.2.2.2.2.1 13 (by decide) (Or.inl (by decide))).trans ha13

end Maxwell.Cost.DecoderParser
