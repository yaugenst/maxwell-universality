import Maxwell.Cost.DecoderParser.Row

namespace Maxwell.Cost.DecoderParser
open Structured
open RationalAccumulator (Bank bankValue)
set_option maxRecDepth 4096

def rowsWork : Finset ℕ := insert 72 termsWork

theorem FlowFrame.mono {work work' : Finset ℕ} {s t : BitRAMState}
    (h : FlowFrame work s t) (hw : work ⊆ work') : FlowFrame work' s t :=
  ⟨h.memory,h.randomCursor,fun i hi => h.tapes i (fun hm => hi (hw hm))⟩

private theorem counter_flow {s t : Store} (h : Counted.Frame 72 s t) : FlowFrame rowsWork s.val t.val :=
  ⟨h.2.2.1,h.2.2.2.1,fun i hi => h.2.2.2.2.2.1 i
    (by simp only [rowsWork,Finset.mem_insert,not_or] at hi;exact hi.1)⟩

private theorem counter_bank {s t : Store} (h : Counted.Frame 72 s t)
    {v : ℕ → ℕ} (hb : Bank s.val v) : Bank t.val v := by
  intro i hi hi'
  exact RationalAccumulator.word_of_eq (h.2.2.2.2.2.1 i (by omega)) (hb i hi hi')

def RowResult {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (A : ℕ) (row : Row D.sampleCount) (pair : Codec.RationalPair) : Prop :=
  pair.value=row.1+termsValue D w row.2 ∧ pair.Short (A+2)

/-- The outer binary countdown evaluates each encoded row exactly once.
All coefficient reads and indexed message fetches occur inside this fixed
finite loop; no row evaluation is delegated to host arithmetic. -/
theorem rows_steps {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (rs : List (Row D.sampleCount)) (bits preceding suffix : List Bool)
    (randomTape : ℕ → Bool) (v : ℕ → ℕ) (A : ℕ) (hv : Algebra.CoreShort A v)
    (hwidth : ∀ row ∈ rs, offsetWidth row.1+termsWidth D w row.2 ≤ A)
    (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0) (s : Store)
    (hh : s.val.inputHead=preceding.length) (hr : EvalReady D.format s.val) (hb : Bank s.val v)
    (hm : BitArray.Represents s.val.memory 0 D.format.width (messageWords D w))
    (h73 : s.val.tapes 73=BitTape.blank)
    (hword : s.val.tapes 72=BitTape.ofList bits) (hvalue : addressValue bits=rs.length) :
    ∃ cost, ∃ t : Store, ∃ v' : ℕ → ℕ, ∃ pairs : List Codec.RationalPair, ∃ finalBits,
      cost ≤ (rs.length+1)*(13*bits.length+15)+(rs.map (rowPrice D w A)).sum ∧
      Executes (preceding++(rs.flatMap rowWire++suffix)) randomTape (Counted.code 72 rowCode) cost s t ∧
      t.val.inputHead=s.val.inputHead+(rs.flatMap rowWire).length ∧
      Bank t.val v' ∧ EvalReady D.format t.val ∧ Algebra.CoreShort A v' ∧
      List.Forall₂ (RowResult D w A) rs pairs ∧
      t.val.output=(pairs.flatMap Codec.RationalPair.encode).reverse++s.val.output ∧
      v' 33=0 ∧ v' 34=0 ∧ v' 35=0 ∧ v' 36=0 ∧
      t.val.tapes 73=BitTape.blank ∧
      t.val.tapes 72=BitTape.ofList finalBits ∧ finalBits.length=bits.length ∧
      FlowFrame rowsWork s.val t.val := by
  induction rs generalizing bits preceding v s with
  | nil =>
    obtain ⟨t,et,ht72,ht29,htf⟩ := Counted.test_executes 72 (preceding++([].flatMap rowWire++suffix)) randomTape s bits hword
    have hz := ht29.mpr hvalue
    refine ⟨_,t,v,[],subtractBit true bits,?_,et.seq (Executes.done hz),?_,counter_bank htf hb,
      hr.counter 72 (by decide) htf,hv,.nil,?_,h33,h34,h35,h36,
      (htf.2.2.2.2.2.1 73 (by decide)).trans h73,ht72,subtractBit_length true bits,counter_flow htf⟩
    · simp
    · simpa using htf.2.1
    · simpa using htf.2.2.2.2.1
  | cons x xs ih =>
    let input := preceding++((x::xs).flatMap rowWire++suffix)
    obtain ⟨u,eu,hu72,hu29,huf⟩ := Counted.test_executes 72 input randomTape s bits hword
    have hpred : addressValue (subtractBit true bits)=xs.length := by
      rw [subtractBit_pred bits (by simp at hvalue;omega),hvalue];simp
    have htrue : u.val.registers 29=true := by
      cases hh : u.val.registers 29 with
      | true => rfl
      | false => have := hu29.mp hh;simp at hvalue;omega
    obtain ⟨rc,a,av,pair,hrc,ea,hah,hab,har,hpair,hpairw,hao,haw,ha33,ha34,ha35,ha36,ha73,haf⟩ :=
      row_steps D w x preceding (xs.flatMap rowWire++suffix) randomTape v A hv h33 h34 h35 h36 u
        (huf.2.1.trans hh) (hr.counter 72 (by decide) huf) (counter_bank huf hb)
        (by simpa [huf.2.2.1] using hm) ((huf.2.2.2.2.2.1 73 (by decide)).trans h73)
    have hinput : preceding++(rowWire x++(xs.flatMap rowWire++suffix))=input := by simp [input,List.append_assoc]
    rw [hinput] at ea
    have hxwidth := hwidth x (by simp)
    have hawA : Algebra.CoreShort A av := ⟨haw.1.trans hxwidth,haw.2.1.trans hxwidth,haw.2.2.trans hxwidth⟩
    obtain ⟨tc,t,v',pairs,fw,htc,et,hth,htb,htr,htw,htpairs,hto,ht33,ht34,ht35,ht36,ht73,ht72,htlen,htf⟩ :=
      ih (subtractBit true bits) (preceding++rowWire x) av hawA
        (by intro row hrow;exact hwidth row (by simp [hrow])) ha33 ha34 ha35 ha36 a
        (by simp [hah,huf.2.1,hh]) har hab (by simpa [haf.memory,huf.2.2.1] using hm) ha73
        ((haf.tapes 72 (by decide)).trans hu72) hpred
    have hrestinput : (preceding++rowWire x)++(xs.flatMap rowWire++suffix)=input := by simp [input,List.append_assoc]
    rw [hrestinput] at et
    change Executes input randomTape (.seq (Counted.test 72) (.loop 29 (.seq rowCode (Counted.test 72)))) tc a t at et
    cases et with
    | seq restTest restLoop =>
      refine ⟨_,t,v',pair::pairs,fw,?_,eu.seq (Executes.more htrue (ea.seq restTest) restLoop),?_,htb,htr,htw,
        .cons ⟨hpair,hpairw.1.trans (by omega),hpairw.2.trans (by omega)⟩ htpairs,?_,
        ht33,ht34,ht35,ht36,ht73,ht72,htlen.trans (subtractBit_length true bits),
        (counter_flow huf).trans ((haf.mono (by intro i hi;exact Finset.mem_insert_of_mem hi)).trans htf)⟩
      · simp only [List.length_cons,List.map_cons,List.sum_cons,subtractBit_length] at *
        nlinarith only [hrc,htc]
      · simp only [List.flatMap_cons,List.length_append] at *
        have hi := huf.2.1
        omega
      · rw [hto,hao,huf.2.2.2.2.1]
        simp [List.flatMap_cons,List.reverse_append,List.append_assoc]

end Maxwell.Cost.DecoderParser
