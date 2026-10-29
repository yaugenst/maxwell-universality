import Maxwell.Cost.DecoderAddressWidth.Row
import Maxwell.Cost.DecoderParser.Rows

namespace Maxwell.Cost.DecoderAddressWidth
open Structured DecoderParser
open RationalAccumulator (Bank)
set_option maxRecDepth 8192

private theorem rows_parts {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (rs : List (Row D.sampleCount)) (bits preceding suffix : List Bool)
    (tape : ℕ→Bool) (v : ℕ→ℕ) (A W : ℕ) (hW : fetchWidth D ≤ W)
    (hv : Algebra.CoreShort A v) (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0)
    (s : Store) (hs : Address.Within W s.val) (hh : s.val.inputHead=preceding.length)
    (hr : EvalReady D.format s.val) (hb : Bank s.val v)
    (hm : BitArray.Represents s.val.memory 0 D.format.width (messageWords D w))
    (h73 : s.val.tapes 73=BitTape.blank) (hword : s.val.tapes 72=BitTape.ofList bits)
    (hvalue : addressValue bits=rs.length) :
    ∃ u cost t,
      Visited W (preceding++(rs.flatMap rowWire++suffix)) tape (Counted.test 72) (13*bits.length+14) s u ∧
      Visited W (preceding++(rs.flatMap rowWire++suffix)) tape
        (.loop 29 (.seq rowCode (Counted.test 72))) cost u t := by
  induction rs generalizing bits preceding v A s with
  | nil =>
    obtain ⟨u,eu,_,hu29,_⟩ := Counted.test_executes 72 (preceding++([].flatMap rowWire++suffix)) tape s bits hword
    have eU := eu.visited_noAddressPush (by decide) hs
    exact ⟨u,1,u,eU,.done (hu29.mpr hvalue) eU.finish⟩
  | cons x xs ih =>
    let input := preceding++((x::xs).flatMap rowWire++suffix)
    obtain ⟨u,eu,hu72,hu29,huf⟩ := Counted.test_executes 72 input tape s bits hword
    have eU := eu.visited_noAddressPush (by decide) hs
    have hpred : addressValue (subtractBit true bits)=xs.length := by
      rw [subtractBit_pred bits (by simp at hvalue;omega),hvalue];simp
    have htrue : u.val.registers 29=true := by
      cases hh : u.val.registers 29 with
      | true => rfl
      | false => have := hu29.mp hh;simp at hvalue;omega
    have hub := bank_counter (by decide) huf hb
    have hur := hr.counter 72 (by decide) huf
    have hu73 : u.val.tapes 73=BitTape.blank := (huf.2.2.2.2.2.1 73 (by decide)).trans h73
    have hum : BitArray.Represents u.val.memory 0 D.format.width (messageWords D w) := by
      simpa [huf.2.2.1] using hm
    obtain ⟨rc,a,av,_,_,ea,hah,hab,har,_,_,_,haw,ha33,ha34,ha35,ha36,ha73,haf⟩ :=
      row_steps D w x preceding (xs.flatMap rowWire++suffix) tape v A hv h33 h34 h35 h36 u
        (huf.2.1.trans hh) hur hub hum hu73
    have eA := row_visited D w x preceding (xs.flatMap rowWire++suffix) tape v W hW
      h33 h34 h35 h36 u a eU.finish (huf.2.1.trans hh) hur hub hum hu73 rc ea
    have hinput : preceding++(rowWire x++(xs.flatMap rowWire++suffix))=input := by simp [input,List.append_assoc]
    rw [hinput] at eA
    obtain ⟨after,tc,t,restTest,restLoop⟩ := ih (subtractBit true bits) (preceding++rowWire x) av
      (offsetWidth x.1+termsWidth D w x.2) haw ha33 ha34 ha35 ha36 a eA.finish
      (by simp [hah,huf.2.1,hh]) har hab (by simpa [haf.memory,huf.2.2.1] using hm) ha73
      ((haf.tapes 72 (by decide)).trans hu72) hpred
    have hrestinput : (preceding++rowWire x)++(xs.flatMap rowWire++suffix)=input := by simp [input,List.append_assoc]
    rw [hrestinput] at restTest restLoop
    exact ⟨u,_,t,eU,.more htrue (eA.seq restTest) restLoop⟩

theorem rows_visited {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (rs : List (Row D.sampleCount)) (bits preceding suffix : List Bool)
    (tape : ℕ→Bool) (v : ℕ→ℕ) (A W : ℕ) (hW : fetchWidth D ≤ W)
    (hv : Algebra.CoreShort A v) (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0)
    (s t : Store) (hs : Address.Within W s.val) (hh : s.val.inputHead=preceding.length)
    (hr : EvalReady D.format s.val) (hb : Bank s.val v)
    (hm : BitArray.Represents s.val.memory 0 D.format.width (messageWords D w))
    (h73 : s.val.tapes 73=BitTape.blank) (hword : s.val.tapes 72=BitTape.ofList bits)
    (hvalue : addressValue bits=rs.length) (cost : ℕ)
    (run : Executes (preceding++(rs.flatMap rowWire++suffix)) tape (Counted.code 72 rowCode) cost s t) :
    Visited W (preceding++(rs.flatMap rowWire++suffix)) tape (Counted.code 72 rowCode) cost s t := by
  obtain ⟨u,_,_,htest,hloop⟩ := rows_parts D w rs bits preceding suffix tape v A W hW
    hv h33 h34 h35 h36 s hs hh hr hb hm h73 hword hvalue
  exact (htest.seq hloop).of_execution run

end Maxwell.Cost.DecoderAddressWidth
