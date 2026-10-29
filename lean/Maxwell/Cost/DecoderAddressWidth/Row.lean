import Maxwell.Cost.DecoderAddressWidth.Terms
import Maxwell.Cost.DecoderParser.Row

namespace Maxwell.Cost.DecoderAddressWidth
open Structured DecoderParser
open RationalAccumulator (Bank Scratch)
set_option maxRecDepth 8192

private theorem ready_header {F : Target.FixedPointFormat} {s t : Store}
    (h : EvalReady F s.val) (hf : DecoderParser.Frame rowWork s.val t.val)
    (hs : Scratch t.val 0) (h12 : t.val.tapes 12=BitTape.blank)
    (h13 : t.val.tapes 13=BitTape.blank) : EvalReady F t.val := by
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

theorem row_visited {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (row : Row D.sampleCount) (preceding suffix : List Bool) (tape : ℕ→Bool)
    (v : ℕ→ℕ) (W : ℕ) (hW : fetchWidth D ≤ W)
    (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0) (s t : Store)
    (hs : Address.Within W s.val) (hh : s.val.inputHead=preceding.length)
    (hr : EvalReady D.format s.val) (hb : Bank s.val v)
    (hm : BitArray.Represents s.val.memory 0 D.format.width (messageWords D w))
    (h73 : s.val.tapes 73=BitTape.blank) (cost : ℕ)
    (run : Executes (preceding++(rowWire row++suffix)) tape rowCode cost s t) :
    Visited W (preceding++(rowWire row++suffix)) tape rowCode cost s t := by
  let input := preceding++(rowWire row++suffix)
  obtain ⟨a,ea,hah,hab,har,ha73,_,ha12,ha13,haf⟩ := rowHeader_steps row.1 row.2.length v preceding
    (row.2.flatMap termWire++suffix) tape s hh hb hr.arithmetic
    (hr.parser 10 (by decide)) (hr.parser 12 (by decide)) (hr.parser 13 (by decide)) h73
  have hi : preceding++(Codec.rat row.1++(Codec.nat row.2.length++(row.2.flatMap termWire++suffix)))=input := by
    simp [input,rowWire,List.append_assoc]
  rw [hi] at ea
  have eA := ea.visited_noAddressPush (by decide) hs
  let av := RationalAccumulator.initialized v (Codec.RationalPair.canonical row.1)
  have had : 0 < av 32 := by simpa [av,RationalAccumulator.initialized,Codec.RationalPair.canonical] using row.1.pos
  have haw := Algebra.initialized_coreShort v (Codec.RationalPair.canonical row.1) (offsetWidth row.1) (canonical_short row.1)
  have haz (i : ℕ) (hi : i=33 ∨ i=34 ∨ i=35 ∨ i=36) : av i=0 := by
    rcases hi with rfl|rfl|rfl|rfl <;>
      cases hz : decide ((Codec.RationalPair.canonical row.1).numerator < 0) <;>
      simp [av,RationalAccumulator.initialized,RationalAccumulator.resetBank,RationalAccumulator.selected,hz,h33,h34,h35,h36]
  have hbi : (preceding++(Codec.rat row.1++Codec.nat row.2.length))++(row.2.flatMap termWire++suffix)=input := by
    simp [input,rowWire,List.append_assoc]
  change Executes input tape (.seq _ (.seq _ _)) cost s t at run
  cases run with
  | seq first rest =>
    rcases ea.deterministic first with ⟨rfl,rfl⟩
    cases rest with
    | seq middle last =>
      rw [←hbi] at middle
      have hT := terms_visited D w row.2 row.2.length.bits
        (preceding++(Codec.rat row.1++Codec.nat row.2.length)) suffix tape av (offsetWidth row.1) W hW
        had haw (haz 33 (by simp)) (haz 34 (by simp)) (haz 35 (by simp)) (haz 36 (by simp)) a _
        eA.finish (by simp [hah,hh]) (ready_header hr haf har ha12 ha13) hab
        (by simpa [haf.memory] using hm) ha73 (RationalAccumulator.address_bits _) _ middle
      rw [hbi] at hT
      exact eA.seq (hT.seq (last.visited_noAddressPush (by decide) hT.finish))

end Maxwell.Cost.DecoderAddressWidth
