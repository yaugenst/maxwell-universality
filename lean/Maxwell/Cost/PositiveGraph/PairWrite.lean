import Maxwell.Cost.PositiveGraph.WriteWord
import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.WordLength

namespace Maxwell.Cost.PositiveGraph.PairWrite
open Structured
open RationalAccumulator (Blank)

def code (indexBank firstSource : ℕ) : Code :=
  .seq (BankArray.writeCanonicalCode 140 indexBank 151 146 firstSource)
    (.seq (BankArray.incrementCode indexBank)
      (.seq (BankArray.writeCanonicalCode 140 indexBank 151 146 121)
        (BankArray.incrementCode indexBank)))

def price (width : List Bool) (index : ℕ) (first mediator : List Bool) : ℕ :=
  BankArray.costCap width index.bits [] (FixedWidth.bits (addressValue width) first) +
  BankArray.costCap width (index+1).bits [] (FixedWidth.bits (addressValue width) mediator) +
  200*addressValue width+12*(index.bits.length+(index+1).bits.length)+236

theorem increment_bits (n : ℕ) : Increment.bits n.bits = (n+1).bits := by
  rw [← WordLength.countBits_eq n,← WordLength.countBits_eq (n+1)]
  rfl

/-- Emit the two actual endpoints of one positive edge, then advance the
saved incidence cursor twice. The payload words may have high zero padding. -/
theorem executes {n : ℕ} (indexBank firstSource : ℕ) (hi : 10 ≤ indexBank) (hf : 10 ≤ firstSource)
    (hi37 : indexBank ≠ 37) (hi140 : indexBank ≠ 140) (hi151 : indexBank ≠ 151)
    (hi146 : indexBank ≠ 146) (hi121 : indexBank ≠ 121)
    (input : List Bool) (randomTape : ℕ → Bool) (width clock first mediator : List Bool)
    (index : ℕ) (hroom : index+1 < n) (words : Vector (List Bool) n) (s : Store)
    (hwidth : 0 < width.length) (hpositive : 0 < addressValue width)
    (hclock : clock.length = addressValue width)
    (hfirst : first.length ≤ addressValue width) (hmediator : mediator.length ≤ addressValue width)
    (hscratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (hwidthBank : BankArray.Word s.val 140 width) (hindex : BankArray.Word s.val indexBank index.bits)
    (hbase : BankArray.Word s.val 151 []) (hclockBank : BankArray.Word s.val 146 clock)
    (hsource : BankArray.Word s.val firstSource first) (hmed : BankArray.Word s.val 121 mediator)
    (harray : BitArray.Represents s.val.memory 0 (addressValue width) words) :
    ∃ cost t, cost ≤ price width index first mediator ∧
      Executes input randomTape (code indexBank firstSource) cost s t ∧
      t.val.memory = MemoryWord.writeBits
        (MemoryWord.writeBits s.val.memory (index*addressValue width)
          (FixedWidth.bits (addressValue width) first))
        ((index+1)*addressValue width) (FixedWidth.bits (addressValue width) mediator) ∧
      BitArray.Represents t.val.memory 0 (addressValue width)
        ((words.set index (FixedWidth.bits (addressValue width) first) (by omega)).set
          (index+1) (FixedWidth.bits (addressValue width) mediator) hroom) ∧
      BankArray.Word t.val indexBank (index+2).bits ∧ BankArray.Scratch t.val ∧
      Blank t.val 7 ∧ Blank t.val 37 ∧ SourceCircuit.Frame {37,indexBank} s.val t.val := by
  obtain ⟨ac,a,acBound,ea,am,aa,ascratch,a7,a37,af⟩ := BankArray.write_word
    140 indexBank 151 146 firstSource (by decide) hi (by decide) (by decide) hf
    (by decide) hi37 (by decide) input randomTape width index.bits [] clock words
    ⟨index,by omega⟩ first hwidth (RationalAccumulator.address_bits _) hclock hpositive hfirst
    s hscratch h7 h37 hwidthBank hindex hbase hclockBank hsource harray
  obtain ⟨bc,b,bcBound,eb,bi,bscratch,bm,_ba,bk,bf⟩ := BankArray.increment_bank indexBank hi
    input randomTape index.bits a
    (BankArray.word_of_eq (af.2.2.2.1 indexBank (Or.inr hi) hi37) hindex) ascratch
  have bi' : BankArray.Word b.val indexBank (index+1).bits := by simpa only [increment_bits] using bi
  have keep (j : ℕ) (hj : 10 ≤ j) (hj37 : j ≠ 37) (hji : j ≠ indexBank) :
      b.val.tapes j = s.val.tapes j := (bk j hji).trans (af.2.2.2.1 j (Or.inr hj) hj37)
  obtain ⟨cc,c,ccBound,ec,cm,ca,cscratch,c7,c37,cf⟩ := BankArray.write_word
    140 indexBank 151 146 121 (by decide) hi (by decide) (by decide) (by decide)
    (by decide) hi37 (by decide) input randomTape width (index+1).bits [] clock
    (words.set index (FixedWidth.bits (addressValue width) first) (by omega))
    ⟨index+1,hroom⟩ mediator hwidth (RationalAccumulator.address_bits _) hclock hpositive hmediator
    b bscratch (RationalAccumulator.blank_of_eq (bk 7 (by omega)) a7)
    (RationalAccumulator.blank_of_eq (bk 37 hi37.symm) a37)
    (BankArray.word_of_eq (keep 140 (by decide) (by decide) hi140.symm) hwidthBank) bi'
    (BankArray.word_of_eq (keep 151 (by decide) (by decide) hi151.symm) hbase)
    (BankArray.word_of_eq (keep 146 (by decide) (by decide) hi146.symm) hclockBank)
    (BankArray.word_of_eq (keep 121 (by decide) (by decide) hi121.symm) hmed)
    (by simpa only [bm] using aa)
  obtain ⟨dc,t,dcBound,et,ti,tscratch,tm,_ta,tk,tf⟩ := BankArray.increment_bank indexBank hi
    input randomTape (index+1).bits c
    (BankArray.word_of_eq (cf.2.2.2.1 indexBank (Or.inr hi) hi37) bi') cscratch
  refine ⟨_,t,?_,ea.seq (eb.seq (ec.seq et)),?_,?_,?_,tscratch,
    RationalAccumulator.blank_of_eq (tk 7 (by omega)) c7,
    RationalAccumulator.blank_of_eq (tk 37 hi37.symm) c37,?_⟩
  · unfold price
    omega
  · simp only [addressValue,zero_add,tm,cm,bm,am]
  · simpa only [tm,addressValue] using ca
  · simpa only [increment_bits,Nat.add_assoc,one_add_one_eq_two] using ti
  · exact (((SourceCircuit.frame_except af).mono (by simp)).trans
      ((SourceCircuit.frame_except bf).mono (by simp))).trans
        (((SourceCircuit.frame_except cf).mono (by simp)).trans
          ((SourceCircuit.frame_except tf).mono (by simp)))

end Maxwell.Cost.PositiveGraph.PairWrite
