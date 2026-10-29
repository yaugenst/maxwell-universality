import Maxwell.Cost.DecoderAddressWidth.Term
import Maxwell.Cost.DecoderParser.Terms

namespace Maxwell.Cost.DecoderAddressWidth
open Structured DecoderParser
open RationalAccumulator (Bank)
set_option maxRecDepth 8192

theorem bank_counter {counter : ℕ} (hc : 70 ≤ counter) {s t : Store}
    (h : Counted.Frame counter s t) {v : ℕ→ℕ} (hb : Bank s.val v) : Bank t.val v := by
  intro i hi hi'
  exact RationalAccumulator.word_of_eq (h.2.2.2.2.2.1 i (by omega)) (hb i hi hi')

private theorem terms_parts {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (terms : List (Fin D.sampleCount × ℚ)) (bits preceding suffix : List Bool)
    (tape : ℕ→Bool) (v : ℕ→ℕ) (A W : ℕ) (hW : fetchWidth D ≤ W)
    (hd : 0 < v 32) (hv : Algebra.CoreShort A v)
    (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0) (s : Store)
    (hs : Address.Within W s.val) (hh : s.val.inputHead=preceding.length)
    (hr : EvalReady D.format s.val) (hb : Bank s.val v)
    (hm : BitArray.Represents s.val.memory 0 D.format.width (messageWords D w))
    (hword : s.val.tapes 73=BitTape.ofList bits) (hvalue : addressValue bits=terms.length) :
    ∃ u cost t,
      Visited W (preceding++(terms.flatMap termWire++suffix)) tape (Counted.test 73) (13*bits.length+14) s u ∧
      Visited W (preceding++(terms.flatMap termWire++suffix)) tape
        (.loop 29 (.seq termCode (Counted.test 73))) cost u t := by
  induction terms generalizing bits preceding v A s with
  | nil =>
    obtain ⟨u,eu,_,hu29,_⟩ := Counted.test_executes 73 (preceding++([].flatMap termWire++suffix)) tape s bits hword
    have eU := eu.visited_noAddressPush (by decide) hs
    exact ⟨u,1,u,eU,.done (hu29.mpr hvalue) eU.finish⟩
  | cons x xs ih =>
    let input := preceding++((x::xs).flatMap termWire++suffix)
    obtain ⟨u,eu,hu73,hu29,huf⟩ := Counted.test_executes 73 input tape s bits hword
    have eU := eu.visited_noAddressPush (by decide) hs
    have hpred : addressValue (subtractBit true bits)=xs.length := by
      rw [subtractBit_pred bits (by simp at hvalue;omega),hvalue];simp
    have htrue : u.val.registers 29=true := by
      cases hh : u.val.registers 29 with
      | true => rfl
      | false => have := hu29.mp hh;simp at hvalue;omega
    obtain ⟨tc,a,av,_,ea,hah,hab,har,_,had,haw,ha33,ha34,ha35,ha36,haf⟩ :=
      term_steps D w x.1 x.2 preceding (xs.flatMap termWire++suffix) tape v A hd hv h33 h34 h35 h36 u
        (huf.2.1.trans hh) (hr.counter 73 (by decide) huf) (bank_counter (by decide) huf hb)
        (by simpa [huf.2.2.1] using hm)
    have eA := term_visited D x.1 x.2 preceding (xs.flatMap termWire++suffix) tape W hW u a
      eU.finish (huf.2.1.trans hh) (hr.counter 73 (by decide) huf) tc ea
    have hinput : preceding++(Codec.nat x.1.val++(Codec.rat x.2++(xs.flatMap termWire++suffix)))=input := by
      simp [input,termWire,List.append_assoc]
    rw [hinput] at eA
    obtain ⟨after,rc,t,restTest,restLoop⟩ :=
      ih (subtractBit true bits) (preceding++termWire x) av
        (A+termWidth D.format x.2 (Codec.word D.format (w x.1))+1) had haw ha33 ha34 ha35 ha36 a
        eA.finish (by simp [termWire,List.length_append] at hah ⊢;rw [hah,huf.2.1,hh])
        har hab (by simpa [haf.memory,huf.2.2.1] using hm)
        ((haf.tapes 73 (by decide)).trans hu73) hpred
    have hrestinput : (preceding++termWire x)++(xs.flatMap termWire++suffix)=input := by simp [input,List.append_assoc]
    rw [hrestinput] at restTest restLoop
    exact ⟨u,_,t,eU,.more htrue (eA.seq restTest) restLoop⟩

theorem terms_visited {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (terms : List (Fin D.sampleCount × ℚ)) (bits preceding suffix : List Bool)
    (tape : ℕ→Bool) (v : ℕ→ℕ) (A W : ℕ) (hW : fetchWidth D ≤ W)
    (hd : 0 < v 32) (hv : Algebra.CoreShort A v)
    (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0) (s t : Store)
    (hs : Address.Within W s.val) (hh : s.val.inputHead=preceding.length)
    (hr : EvalReady D.format s.val) (hb : Bank s.val v)
    (hm : BitArray.Represents s.val.memory 0 D.format.width (messageWords D w))
    (hword : s.val.tapes 73=BitTape.ofList bits) (hvalue : addressValue bits=terms.length)
    (cost : ℕ) (run : Executes (preceding++(terms.flatMap termWire++suffix)) tape
      (Counted.code 73 termCode) cost s t) :
    Visited W (preceding++(terms.flatMap termWire++suffix)) tape (Counted.code 73 termCode) cost s t := by
  obtain ⟨u,_,_,htest,hloop⟩ := terms_parts D w terms bits preceding suffix tape v A W hW
    hd hv h33 h34 h35 h36 s hs hh hr hb hm hword hvalue
  exact (htest.seq hloop).of_execution run

end Maxwell.Cost.DecoderAddressWidth
