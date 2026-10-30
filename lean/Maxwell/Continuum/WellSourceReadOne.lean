import Maxwell.Continuum.WellSourceReadMetadata
import Maxwell.Cost.IncidencePass.Common

/-! One original-source field is read by fixed code. True selects the
four-bit diagonal code; false selects the two-bit saved incidence count. -/
namespace Maxwell.Continuum.RationalDataflow.WellSourceRead
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def wordWidth (diagonal : Bool) : ℕ := if diagonal then 4 else 2
def wordClock (diagonal : Bool) : ℕ := if diagonal then 8 else 2
def baseTape (diagonal : Bool) : ℕ := if diagonal then 993 else 994
def targetSlot (diagonal : Bool) : ℕ := if diagonal then 8 else 9

def readCode (diagonal : Bool) : Code :=
  .seq (NatAssign.code (prepare (wordWidth diagonal) (wordClock diagonal)))
    (NaturalArrayRead.code 995 998 (baseTape diagonal) 996 (targetSlot diagonal))

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  four : t.tapes 4=s.tapes 4
  tapes : ∀i,10 ≤ i→i≠995→i≠996→i∉ports WellStrength.bank→t.tapes i=s.tapes i

theorem readCode_four (diagonal : Bool) : (readCode diagonal).protectsTape 4=true := by
  cases diagonal <;> decide

theorem Frame.trans {s t u : BitRAMState} (f : Frame s t) (g : Frame t u) : Frame s u :=
  ⟨g.memory.trans f.memory,g.inputHead.trans f.inputHead,g.randomCursor.trans f.randomCursor,
    g.output.trans f.output,g.four.trans f.four,
    fun i hi h995 h996 hp=>(g.tapes i hi h995 h996 hp).trans (f.tapes i hi h995 h996 hp)⟩

theorem read_executes {n : ℕ} (diagonal : Bool) (a : Vector (List Bool) n)
    (base B : ℕ) (hB : 4≤B) (hb : base.bits.length≤B) (index : List Bool)
    (hlen : index.length≤B) (i : Fin n) (hi : addressValue index=i.val)
    (v : ℕ→Parts) (hv : WidthBank WellStrength.bank B v) (hg : Good WellStrength.bank v)
    (m : ℕ→ℕ) (hm : ∀j∈metaIds,(m j).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready WellStrength.bank v s) (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (hmeta : NatAssign.Bank metaIds m s.val) (hbase : Word s.val (baseTape diagonal) base)
    (hindex : BankArray.Word s.val 998 index)
    (ha : BitArray.Represents s.val.memory base (wordWidth diagonal) a) :
    ∃cost t,Executes input tape (readCode diagonal) cost s t ∧ cost≤2^21*(B+3)^2 ∧
      Ready WellStrength.bank (NaturalArrayRead.values v (targetSlot diagonal) (addressValue (a.get i))) t ∧
      Good WellStrength.bank (NaturalArrayRead.values v (targetSlot diagonal) (addressValue (a.get i))) ∧
      WidthBank WellStrength.bank B (NaturalArrayRead.values v (targetSlot diagonal) (addressValue (a.get i))) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      NatAssign.Bank metaIds (prepared (wordWidth diagonal) (wordClock diagonal) m) t.val ∧ Frame s.val t.val := by
  have hw : (wordWidth diagonal).bits.length≤B := by cases diagonal <;> simp only [wordWidth,Bool.false_eq_true,↓reduceIte] <;> omega
  have hc : (wordClock diagonal).bits.length≤B := by cases diagonal <;> simp only [wordClock,Bool.false_eq_true,↓reduceIte] <;> omega
  have hwpos : 0<(wordWidth diagonal).bits.length := by cases diagonal <;> decide
  have clockLength : (wordClock diagonal).bits.length=wordWidth diagonal := by cases diagonal <;> decide
  have hwidth : wordWidth diagonal≤B := by cases diagonal <;> simp [wordWidth] <;> omega
  have targetMem : targetSlot diagonal∈WellStrength.bank := by cases diagonal <;> decide
  have hgbase : 10≤baseTape diagonal ∧ baseTape diagonal<1000 := by cases diagonal <;> decide
  obtain ⟨c0,u,e0,hc0,r0,s0,z0,b0,f0⟩ := prepare_executes (wordWidth diagonal) (wordClock diagonal) B
    hw hc v m hm input tape s hr hs h7 hmeta
  have width0 : BankArray.Word u.val 995 (wordWidth diagonal).bits := by
    simpa only [prepared_width] using b0 995 (by decide)
  have clock0 : BankArray.Word u.val 996 (wordClock diagonal).bits := by
    simpa only [prepared_clock] using b0 996 (by decide)
  have base0 : BankArray.Word u.val (baseTape diagonal) base.bits :=
    RationalAccumulator.word_of_eq (f0.tapes _ (by cases diagonal <;> decide)) hbase
  have index0 := BankArray.word_of_eq (f0.tapes 998 (by decide)) hindex
  obtain ⟨c1,t,e1,hc1,r1,s1,z1,f1⟩ := NaturalArrayRead.executes WellStrength.bank
    (targetSlot diagonal) 995 998 (baseTape diagonal) 996 targetMem (by decide) (by decide) hgbase (by decide)
    (wordWidth diagonal).bits index base.bits (wordClock diagonal).bits a i hwpos hi
    (by simpa only [addressValue_bits] using clockLength) v input tape u r0 s0 z0 width0 index0 base0 clock0
    (by simpa only [f0.memory,addressValue_bits] using ha)
  have ex := e0.seq e1
  have hp := positivePort_ge (targetSlot diagonal)
  have frame : Frame s.val t.val := by
    refine ⟨f1.memory.trans f0.memory,f1.inputHead.trans f0.inputHead,
      f1.randomCursor.trans f0.randomCursor,f1.output.trans f0.output,
      ex.protectsTape 4 (readCode_four diagonal),?_⟩
    intro k hk h995 h996 hports
    have htarget : k≠positivePort (targetSlot diagonal) := by
      intro he
      exact hports (Finset.mem_biUnion.mpr ⟨_,targetMem,by simp [he,cellPorts]⟩)
    exact (f1.tapes k hk htarget).trans (f0.tapes k (by simp [metaChanged,metaIds];omega))
  refine ⟨c0+c1,t,ex,?_,r1,NaturalArrayRead.values_valid hg _ _,?_,s1,z1,?_,frame⟩
  · have harr := IncidencePass.array_cost_le (wordWidth diagonal).bits index base.bits (wordClock diagonal).bits B
      hw hlen hb hc (by simpa only [addressValue_bits] using hwidth)
    have hvp := (hv _ targetMem).1
    simp only [addressValue_bits] at hc1
    nlinarith only [hc0,hc1,harr,hvp,hwidth,Nat.zero_le B]
  · intro k hk
    by_cases he : k=targetSlot diagonal
    · subst k
      have hbits : (addressValue (a.get i)).bits.length≤wordWidth diagonal := by
        rw [Nat.size_eq_bits_len]
        apply Nat.size_le.mpr
        simpa only [ha.length i] using Subtraction.addressValue_lt_pow_length (a.get i)
      exact ⟨hbits.trans hwidth,(hv _ hk).2.1,(hv _ hk).2.2⟩
    · simpa only [NaturalArrayRead.values,Function.update_of_ne he] using hv k hk
  · intro k hk
    have hsmall : 10 ≤ k ∧ k<1000 := by simp only [metaIds,Finset.mem_insert,Finset.mem_singleton] at hk;omega
    exact RationalAccumulator.word_of_eq (f1.tapes k hsmall.1 (by omega)) (b0 k hk)

#print axioms read_executes
end Maxwell.Continuum.RationalDataflow.WellSourceRead
