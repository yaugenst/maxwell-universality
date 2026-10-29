import Maxwell.Cost.DecoderParser.Plan
import Maxwell.Cost.RationalAccumulator.EmitCleanup

namespace Maxwell.Cost.DecoderParser
open Structured
open RationalAccumulator (Bank Scratch Word Blank bankValue)
set_option maxRecDepth 4096

structure FlowFrame (work : Finset ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  randomCursor : t.randomCursor=s.randomCursor
  tapes : ∀ i, i ∉ work → t.tapes i=s.tapes i

theorem FlowFrame.trans {work : Finset ℕ} {s t u : BitRAMState}
    (h : FlowFrame work s t) (k : FlowFrame work t u) : FlowFrame work s u :=
  ⟨k.memory.trans h.memory,k.randomCursor.trans h.randomCursor,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

theorem EvalFrame.flow {work : Finset ℕ} {s t : BitRAMState} (h : EvalFrame work s t) : FlowFrame work s t :=
  ⟨h.memory,h.randomCursor,h.tapes⟩

def offsetWidth (q : ℚ) : ℕ := 1+q.num.natAbs.bits.length+q.den.bits.length

theorem canonical_short (q : ℚ) : (Codec.RationalPair.canonical q).Short (offsetWidth q) := by
  simp only [Codec.RationalPair.Short,Codec.RationalPair.canonical,signedBitLength,
    Codec.unsignedBitLength_eq_size,Nat.size_eq_bits_len,offsetWidth]
  omega

def rowCode : Code := .seq rowHeaderCode (.seq (Counted.code 73 termCode)
  (.seq (clearWord 73) RationalAccumulator.emitCleanCode))

def rowPrice {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (oldWidth : ℕ) (row : Row D.sampleCount) : ℕ :=
  18*oldWidth+38*(row.1.num.natAbs.bits.length+row.1.den.bits.length)+21*row.2.length.bits.length+96+
    ((row.2.length+1)*(13*row.2.length.bits.length+15)+termsPrice D w row.2 (offsetWidth row.1)+
      (11*row.2.length.bits.length+10+400*(3*(offsetWidth row.1+termsWidth D w row.2)+4)))

private theorem ready_header {F : Target.FixedPointFormat} {s t : Store}
    (h : EvalReady F s.val) (hf : Frame rowWork s.val t.val)
    (hs : Scratch t.val 0) (h12 : t.val.tapes 12=BitTape.blank) (h13 : t.val.tapes 13=BitTape.blank) :
    EvalReady F t.val := by
  refine ⟨hs,?_,?_,RationalAccumulator.word_of_eq (hf.tapes 64 (by decide)) h.width,
    RationalAccumulator.word_of_eq (hf.tapes 66 (by decide)) h.center,
    RationalAccumulator.word_of_eq (hf.tapes 67 (by decide)) h.scale⟩
  · intro i hi
    exact RationalAccumulator.blank_of_eq (hf.tapes i (by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide)) (h.blank i hi)
  · intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact (hf.tapes 10 (by decide)).trans (h.parser 10 (by decide))
    · exact h12
    · exact h13
    · exact (hf.tapes 45 (by decide)).trans (h.parser 45 (by decide))

private theorem ready_clear {F : Target.FixedPointFormat} {s t : Store}
    (h : EvalReady F s.val) (hf : Frame {73} s.val t.val) : EvalReady F t.val := by
  refine ⟨hf.scratch (by intro i hi;simp;omega) h.arithmetic,?_,?_,
    RationalAccumulator.word_of_eq (hf.tapes 64 (by decide)) h.width,
    RationalAccumulator.word_of_eq (hf.tapes 66 (by decide)) h.center,
    RationalAccumulator.word_of_eq (hf.tapes 67 (by decide)) h.scale⟩
  · intro i hi
    exact RationalAccumulator.blank_of_eq (hf.tapes i (by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi; simp;omega)) (h.blank i hi)
  · intro i hi
    exact (hf.tapes i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;simp;omega)).trans (h.parser i hi)

private theorem ready_emit {F : Target.FixedPointFormat} {s t : Store}
    (h : EvalReady F s.val) (hf : RationalAccumulator.EmitFrame s.val t.val)
    (hs : Scratch t.val 0) : EvalReady F t.val := by
  refine ⟨hs,?_,?_,RationalAccumulator.word_of_eq (hf.2.2.2.2.1 64 (by decide)) h.width,
    RationalAccumulator.word_of_eq (hf.2.2.2.2.1 66 (by decide)) h.center,
    RationalAccumulator.word_of_eq (hf.2.2.2.2.1 67 (by decide)) h.scale⟩
  · intro i hi
    exact RationalAccumulator.blank_of_eq (hf.2.2.2.2.1 i (by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)) (h.blank i hi)
  · intro i hi
    exact (hf.2.2.2.2.1 i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)).trans (h.parser i hi)

/-- A complete actual row, from its encoded offset and support count through
indexed message access to exact raw-rational output. -/
theorem row_steps {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (row : Row D.sampleCount) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (v : ℕ → ℕ) (A : ℕ) (hv : Algebra.CoreShort A v)
    (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0) (s : Store)
    (hh : s.val.inputHead=preceding.length) (hr : EvalReady D.format s.val) (hb : Bank s.val v)
    (hm : BitArray.Represents s.val.memory 0 D.format.width (messageWords D w))
    (h73 : s.val.tapes 73=BitTape.blank) :
    ∃ cost, ∃ t : Store, ∃ v' : ℕ → ℕ, ∃ pair : Codec.RationalPair,
      cost ≤ rowPrice D w A row ∧
      Executes (preceding++(rowWire row++suffix)) randomTape rowCode cost s t ∧
      t.val.inputHead=s.val.inputHead+(rowWire row).length ∧
      Bank t.val v' ∧ EvalReady D.format t.val ∧
      pair.value=row.1+termsValue D w row.2 ∧
      pair.Short (offsetWidth row.1+termsWidth D w row.2+2) ∧
      t.val.output=pair.encode.reverse++s.val.output ∧
      Algebra.CoreShort (offsetWidth row.1+termsWidth D w row.2) v' ∧
      v' 33=0 ∧ v' 34=0 ∧ v' 35=0 ∧ v' 36=0 ∧
      t.val.tapes 73=BitTape.blank ∧ FlowFrame termsWork s.val t.val := by
  let input := preceding++(rowWire row++suffix)
  obtain ⟨a,ea,hah,hab,har,ha73,ha10,ha12,ha13,haf⟩ := rowHeader_steps row.1 row.2.length v preceding
    (row.2.flatMap termWire++suffix) randomTape s hh hb hr.arithmetic
    (hr.parser 10 (by decide)) (hr.parser 12 (by decide)) (hr.parser 13 (by decide)) h73
  have hi : preceding++(Codec.rat row.1++(Codec.nat row.2.length++(row.2.flatMap termWire++suffix)))=input := by
    simp [input,rowWire,List.append_assoc]
  rw [hi] at ea
  let av := RationalAccumulator.initialized v (Codec.RationalPair.canonical row.1)
  have had : 0 < av 32 := by simpa [av,RationalAccumulator.initialized,Codec.RationalPair.canonical] using row.1.pos
  have haw := Algebra.initialized_coreShort v (Codec.RationalPair.canonical row.1) (offsetWidth row.1) (canonical_short row.1)
  obtain ⟨tc,b,bv,fw,htc,eb,hbh,hbb,hbr,hbv,hbd,hbw,hb33,hb34,hb35,hb36,hb73,hblen,hbf⟩ :=
    terms_steps D w row.2 row.2.length.bits (preceding++(Codec.rat row.1++Codec.nat row.2.length)) suffix randomTape
      av (offsetWidth row.1) had haw
      (by cases hz : decide ((Codec.RationalPair.canonical row.1).numerator < 0) <;> simpa [av,RationalAccumulator.initialized,RationalAccumulator.resetBank,RationalAccumulator.selected,hz] using h33)
      (by cases hz : decide ((Codec.RationalPair.canonical row.1).numerator < 0) <;> simpa [av,RationalAccumulator.initialized,RationalAccumulator.resetBank,RationalAccumulator.selected,hz] using h34)
      (by cases hz : decide ((Codec.RationalPair.canonical row.1).numerator < 0) <;> simpa [av,RationalAccumulator.initialized,RationalAccumulator.resetBank,RationalAccumulator.selected,hz] using h35)
      (by cases hz : decide ((Codec.RationalPair.canonical row.1).numerator < 0) <;> simpa [av,RationalAccumulator.initialized,RationalAccumulator.resetBank,RationalAccumulator.selected,hz] using h36)
      a (by simp [hah,hh]) (ready_header hr haf har ha12 ha13) hab
      (by simpa [haf.memory] using hm) ha73 (RationalAccumulator.address_bits _)
  have hbi : (preceding++(Codec.rat row.1++Codec.nat row.2.length))++(row.2.flatMap termWire++suffix)=input := by
    simp [input,rowWire,List.append_assoc]
  rw [hbi] at eb
  obtain ⟨c,ec,hc73,hch,hcf⟩ := clearWord_steps 73 input randomTape fw b hb73
  have hcb := hcf.bank (by intro i hi hi';simp;omega) hbb
  have hcr := ready_clear hbr hcf
  obtain ⟨oc,t,hoc,et,hto,htb,htr,htf⟩ := RationalAccumulator.emit_clean_bank input randomTape bv hbd c hcb hcr.arithmetic
  have hframe : EvalFrame termsWork s.val c.val :=
    (haf.eval.mono (by intro i hi;simp only [rowWork,Finset.mem_insert,Finset.mem_singleton] at hi;rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)).trans
      (hbf.trans (hcf.eval.mono (by simp [termsWork])))
  refine ⟨_,t,bv,RationalAccumulator.emitPair bv hbd,?_,ea.seq (eb.seq (ec.seq et)),?_,htb,
    ready_emit hcr htf htr,?_,?_,?_,hbw,hb33,hb34,hb35,hb36,
    (htf.2.2.2.2.1 73 (by decide)).trans hc73,?_⟩
  · have hhead : rowHeaderPrice v row.1 row.2.length ≤
        18*A+38*(row.1.num.natAbs.bits.length+row.1.den.bits.length)+21*row.2.length.bits.length+96 := by
      dsimp [rowHeaderPrice];rcases hv with ⟨h0,h1,h2⟩;omega
    have hemit : oc ≤ 400*(3*(offsetWidth row.1+termsWidth D w row.2)+4) := hoc.trans (by
      rcases hbw with ⟨h0,h1,h2⟩;omega)
    dsimp [rowPrice]
    rw [hblen]
    omega
  · have ho := htf.2.1
    simp only [rowWire,List.length_append] at *
    omega
  · have hp : (RationalAccumulator.emitPair bv hbd).value=bankValue bv := by
      simp [RationalAccumulator.emitPair,Codec.RationalPair.value,bankValue]
    rw [hp,hbv]
    change bankValue (RationalAccumulator.initialized v (Codec.RationalPair.canonical row.1))+_= _
    rw [RationalAccumulator.initialized_value,Codec.RationalPair.canonical_value]
  · exact Algebra.bankPair_short bv hbd _ hbw
  · rw [hto,hframe.output]
  · exact ⟨htf.2.2.1.trans hframe.memory,htf.2.2.2.1.trans hframe.randomCursor,
      fun i hi => (htf.2.2.2.2.1 i (by simp only [termsWork,termWork,Finset.mem_insert,Finset.mem_singleton,not_or] at hi;omega)).trans (hframe.tapes i hi)⟩

end Maxwell.Cost.DecoderParser
