import Maxwell.Cost.DecoderParser.Term

namespace Maxwell.Cost.DecoderParser
open Structured
open RationalAccumulator (Bank bankValue)
set_option maxRecDepth 4096

def termWire {N : ℕ} (x : Fin N × ℚ) : List Bool := Codec.nat x.1.val++Codec.rat x.2

def termsWidth {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (terms : List (Fin D.sampleCount × ℚ)) : ℕ :=
  (terms.map (fun x => termWidth D.format x.2 (Codec.word D.format (w x.1))+1)).sum

def termsPrice {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages) :
    List (Fin D.sampleCount × ℚ) → ℕ → ℕ
  | [],_ => 0
  | x::xs,A => termPrice D.format x.1.val x.2 (Codec.word D.format (w x.1)) A+
      termsPrice D w xs (A+termWidth D.format x.2 (Codec.word D.format (w x.1))+1)

def termsValue {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (terms : List (Fin D.sampleCount × ℚ)) : ℚ :=
  (terms.map (fun x => x.2*D.format.value (w x.1))).sum

def termsWork : Finset ℕ := insert 73 termWork

private theorem counter_eval {s t : Store} (h : Counted.Frame 73 s t) : EvalFrame termsWork s.val t.val :=
  ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,fun i hi => h.2.2.2.2.2.1 i
    (by simp only [termsWork,Finset.mem_insert,not_or] at hi;exact hi.1)⟩

private theorem counter_bank {s t : Store} (h : Counted.Frame 73 s t)
    {v : ℕ → ℕ} (hb : Bank s.val v) : Bank t.val v := by
  intro i hi hi'
  exact RationalAccumulator.word_of_eq (h.2.2.2.2.2.1 i (by omega)) (hb i hi hi')

/-- A single fixed countdown program evaluates the actual sequential support
records. Its loop count comes from the parsed binary counter on tape73. -/
theorem terms_steps {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (terms : List (Fin D.sampleCount × ℚ)) (bits preceding suffix : List Bool)
    (randomTape : ℕ → Bool) (v : ℕ → ℕ) (A : ℕ)
    (hd : 0 < v 32) (hv : Algebra.CoreShort A v)
    (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0) (s : Store)
    (hh : s.val.inputHead=preceding.length) (hr : EvalReady D.format s.val) (hb : Bank s.val v)
    (hm : BitArray.Represents s.val.memory 0 D.format.width (messageWords D w))
    (hword : s.val.tapes 73=BitTape.ofList bits) (hvalue : addressValue bits=terms.length) :
    ∃ cost, ∃ t : Store, ∃ v' : ℕ → ℕ, ∃ finalBits,
      cost ≤ (terms.length+1)*(13*bits.length+15)+termsPrice D w terms A ∧
      Executes (preceding++(terms.flatMap termWire++suffix)) randomTape (Counted.code 73 termCode) cost s t ∧
      t.val.inputHead=s.val.inputHead+(terms.flatMap termWire).length ∧
      Bank t.val v' ∧ EvalReady D.format t.val ∧
      bankValue v'=bankValue v+termsValue D w terms ∧
      0 < v' 32 ∧ Algebra.CoreShort (A+termsWidth D w terms) v' ∧
      v' 33=0 ∧ v' 34=0 ∧ v' 35=0 ∧ v' 36=0 ∧
      t.val.tapes 73=BitTape.ofList finalBits ∧ finalBits.length=bits.length ∧
      EvalFrame termsWork s.val t.val := by
  induction terms generalizing bits preceding v A s with
  | nil =>
    obtain ⟨t,et,ht73,ht29,htf⟩ := Counted.test_executes 73 (preceding++([].flatMap termWire++suffix)) randomTape s bits hword
    have hz := ht29.mpr hvalue
    refine ⟨_,t,v,subtractBit true bits,?_,et.seq (Executes.done hz),?_,counter_bank htf hb,
      hr.counter 73 (by decide) htf,?_,hd,?_,h33,h34,h35,h36,ht73,subtractBit_length true bits,counter_eval htf⟩
    · simp [termsPrice]
    · simpa using htf.2.1
    · simp [termsValue]
    · simpa [termsWidth] using hv
  | cons x xs ih =>
    let input := preceding++((x::xs).flatMap termWire++suffix)
    obtain ⟨u,eu,hu73,hu29,huf⟩ := Counted.test_executes 73 input randomTape s bits hword
    have hpred : addressValue (subtractBit true bits)=xs.length := by
      rw [subtractBit_pred bits (by simp at hvalue;omega),hvalue];simp
    have htrue : u.val.registers 29=true := by
      cases hh : u.val.registers 29 with
      | true => rfl
      | false => have := hu29.mp hh;simp at hvalue;omega
    obtain ⟨tc,a,av,htc,ea,hah,hab,har,hav,had,haw,ha33,ha34,ha35,ha36,haf⟩ :=
      term_steps D w x.1 x.2 preceding (xs.flatMap termWire++suffix) randomTape v A hd hv h33 h34 h35 h36 u
        (huf.2.1.trans hh) (hr.counter 73 (by decide) huf) (counter_bank huf hb)
        (by simpa [huf.2.2.1] using hm)
    have hinput : preceding++(Codec.nat x.1.val++(Codec.rat x.2++(xs.flatMap termWire++suffix)))=input := by
      simp [input,termWire,List.append_assoc]
    rw [hinput] at ea
    obtain ⟨rc,t,v',fw,hrc,et,hth,htb,htr,htv,htd,htw,ht33,ht34,ht35,ht36,ht73,htlen,htf⟩ :=
      ih (subtractBit true bits) (preceding++termWire x) av
        (A+termWidth D.format x.2 (Codec.word D.format (w x.1))+1) had haw ha33 ha34 ha35 ha36 a
        (by simp [termWire,List.length_append] at hah ⊢;rw [hah,huf.2.1,hh])
        har hab (by simpa [haf.memory,huf.2.2.1] using hm)
        ((haf.tapes 73 (by decide)).trans hu73) hpred
    have hrestinput : (preceding++termWire x)++(xs.flatMap termWire++suffix)=input := by simp [input,List.append_assoc]
    rw [hrestinput] at et
    change Executes input randomTape (.seq (Counted.test 73) (.loop 29 (.seq termCode (Counted.test 73)))) rc a t at et
    cases et with
    | seq restTest restLoop =>
      refine ⟨_,t,v',fw,?_,eu.seq (Executes.more htrue (ea.seq restTest) restLoop),?_,htb,htr,?_,htd,?_,
        ht33,ht34,ht35,ht36,ht73,htlen.trans (subtractBit_length true bits),
        (counter_eval huf).trans ((haf.mono (by intro i hi;exact Finset.mem_insert_of_mem hi)).trans htf)⟩
      · simp only [List.length_cons,subtractBit_length,termsPrice] at *
        nlinarith only [htc,hrc]
      · simp only [List.flatMap_cons,List.length_append,termWire] at *
        have hi := huf.2.1
        omega
      · simp only [termsValue,List.map_cons,List.sum_cons] at *
        rw [htv,hav]
        ring
      · simpa [termsWidth,List.map_cons,List.sum_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using htw

end Maxwell.Cost.DecoderParser
