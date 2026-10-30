import Maxwell.Continuum.SourceRoutingArchiveFrame
import Maxwell.Cost.BankArray.ReadCanonical
import Maxwell.Cost.IncidencePass.Common

/-! Actual endpoint/rank reads for a routing incidence. Both fixed-width
words are normalized before the natural arithmetic program consumes them. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Scatter
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

structure Descriptor (l : IncidenceEncoding.Layout) (clock : List Bool) (s : BitRAMState) : Prop where
  width : Word s 140 l.endpointWidth
  endpointBase : Word s 151 l.baseEndpoint
  clockWord : BankArray.Word s 146 clock
  clock_length : clock.length=l.endpointWidth
  rankBase : Word s 144 l.baseRank
  two : Word s 149 2
  twoClock : Word s 150 2

theorem Descriptor.transport {l : IncidenceEncoding.Layout} {clock : List Bool} {s t : BitRAMState}
    (h : Descriptor l clock s)
    (keep : ∀i,i∈({140,144,146,149,150,151}:Finset ℕ)→t.tapes i=s.tapes i) : Descriptor l clock t :=
  ⟨RationalAccumulator.word_of_eq (keep 140 (by decide)) h.width,
    RationalAccumulator.word_of_eq (keep 151 (by decide)) h.endpointBase,
    BankArray.word_of_eq (keep 146 (by decide)) h.clockWord,h.clock_length,
    RationalAccumulator.word_of_eq (keep 144 (by decide)) h.rankBase,
    RationalAccumulator.word_of_eq (keep 149 (by decide)) h.two,
    RationalAccumulator.word_of_eq (keep 150 (by decide)) h.twoClock⟩

theorem read_array {n : ℕ} (widthBank indexBank baseBank clockBank target : ℕ)
    (hwb : 10 ≤ widthBank) (hib : 10 ≤ indexBank) (hbb : 10 ≤ baseBank)
    (hcb : 10 ≤ clockBank) (ht : 10 ≤ target) (ht37 : target≠37) (ht752 : target≠752)
    (width base : ℕ) (clock : List Bool) (values : Vector ℕ n) (i : Fin n)
    (hw : 0<width) (hc : clock.length=width) (hv : values.get i<2^width)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready s.val)
    (hb : Blank s.val target) (hwidth : Word s.val widthBank width)
    (hindex : Word s.val indexBank i.val) (hbase : Word s.val baseBank base)
    (hclock : BankArray.Word s.val clockBank clock)
    (harray : BitArray.Represents s.val.memory base width (IncidenceEncoding.words width values)) :
    ∃steps t, Executes input tape (BankArray.readCanonicalCode widthBank indexBank baseBank clockBank target)
        steps s t ∧
      steps≤BankArray.costCap width.bits i.val.bits base.bits clock+32*width+35 ∧
      Word t.val target (values.get i) ∧ Ready t.val ∧ t.val.memory=s.val.memory ∧
      ArchiveFrame {target} s.val t.val := by
  obtain ⟨steps,t,hcost,he,hvalue,hz,h7,hm,_ha,hf⟩ := BankArray.read_canonical
    widthBank indexBank baseBank clockBank target hwb hib hbb hcb ht input tape width.bits i.val.bits
    base.bits clock (IncidenceEncoding.words width values) i (RationalAccumulator.bits_nonempty hw)
    (addressValue_bits _) (by simpa only [addressValue_bits] using hc) s hs.scratch hs.seven hb
    hwidth hindex hbase hclock (by simpa only [addressValue_bits] using harray)
  rw [IncidenceEncoding.words_value width values i hv] at hvalue
  have frame := ArchiveFrame.of_bank hf
  refine ⟨steps,t,he,?_,hvalue,⟨hz,h7,?_,?_⟩,hm,frame⟩
  · simpa only [addressValue_bits] using hcost
  · exact RationalAccumulator.blank_of_eq (frame.tapes 37 (by decide) (by simpa using Ne.symm ht37)) hs.pack
  · exact RationalAccumulator.blank_of_eq (frame.tapes 752 (by decide) (by simpa using Ne.symm ht752)) hs.probe

def readCode : Code := .seq (BankArray.readCanonicalCode 140 733 151 146 734)
  (BankArray.readCanonicalCode 149 733 144 150 735)
def readCost (l : IncidenceEncoding.Layout) (clock : List Bool) (i : ℕ) : ℕ :=
  BankArray.costCap l.endpointWidth.bits i.bits l.baseEndpoint.bits clock+32*l.endpointWidth+35+
    (BankArray.costCap (2 : ℕ).bits i.bits l.baseRank.bits (2 : ℕ).bits+99)

theorem read_inputs {n : ℕ} (l : IncidenceEncoding.Layout) (clock : List Bool)
    (endpoint rank : Vector ℕ n) (i : Fin n) (hw : 0<l.endpointWidth)
    (hefit : endpoint.get i<2^l.endpointWidth) (hrfit : rank.get i<4)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready s.val)
    (hd : Descriptor l clock s.val) (hi : Word s.val 733 i.val)
    (h734 : Blank s.val 734) (h735 : Blank s.val 735)
    (he : BitArray.Represents s.val.memory l.baseEndpoint l.endpointWidth
      (IncidenceEncoding.words l.endpointWidth endpoint))
    (hr : BitArray.Represents s.val.memory l.baseRank 2 (IncidenceEncoding.words 2 rank)) :
    ∃steps t, Executes input tape readCode steps s t ∧ steps≤readCost l clock i.val ∧
      Word t.val 734 (endpoint.get i) ∧ Word t.val 735 (rank.get i) ∧
      Ready t.val ∧ t.val.memory=s.val.memory ∧ ArchiveFrame {734,735} s.val t.val := by
  obtain ⟨ca,a,ea,hca,a734,ra,ma,fa⟩ := read_array 140 733 151 146 734
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    l.endpointWidth l.baseEndpoint clock endpoint i hw hd.clock_length hefit input tape s hs h734
    hd.width hi hd.endpointBase hd.clockWord he
  have da := hd.transport (fun k hk => fa.tapes k (Or.inr (by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk; omega)) (by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk ⊢; omega))
  have ai := RationalAccumulator.word_of_eq (fa.tapes 733 (by decide) (by decide)) hi
  have a735 := RationalAccumulator.blank_of_eq (fa.tapes 735 (by decide) (by decide)) h735
  have ar : BitArray.Represents a.val.memory l.baseRank 2 (IncidenceEncoding.words 2 rank) := by
    rw [ma]; exact hr
  obtain ⟨cb,t,eb,hcb,t735,rt,mt,fb⟩ := read_array 149 733 144 150 735
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    2 l.baseRank (2 : ℕ).bits rank i (by decide) (by decide) hrfit input tape a ra a735
    da.two ai da.rankBase da.twoClock ar
  refine ⟨ca+cb,t,ea.seq eb,?_,
    RationalAccumulator.word_of_eq (fb.tapes 734 (by decide) (by decide)) a734,
    t735,rt,mt.trans ma,(fa.mono (by decide)).trans (fb.mono (by decide))⟩
  unfold readCost
  omega

theorem readCost_bound (l : IncidenceEncoding.Layout) (clock : List Bool) (i B : ℕ)
    (hB : 2≤B) (hw : l.endpointWidth≤B) (hc : clock.length=l.endpointWidth)
    (hi : i.bits.length≤B) (he : l.baseEndpoint.bits.length≤B) (hr : l.baseRank.bits.length≤B) :
    readCost l clock i≤80000*(B+2)^2 := by
  have hwidth : l.endpointWidth.bits.length≤B := (natural_bits_length_le _).trans hw
  have ha := IncidencePass.array_cost_le l.endpointWidth.bits i.bits l.baseEndpoint.bits clock B
    hwidth hi he (by omega) (by simpa only [addressValue_bits] using hw)
  have hb := IncidencePass.array_cost_le (2 : ℕ).bits i.bits l.baseRank.bits (2 : ℕ).bits B
    (by simpa only [show (2 : ℕ).bits.length=2 by decide] using hB) hi hr
    (by simpa only [show (2 : ℕ).bits.length=2 by decide] using hB) (by simpa only [addressValue_bits] using hB)
  unfold readCost
  nlinarith

#print axioms read_inputs
#print axioms readCost_bound

end Maxwell.Cost.RoutingPorts.Complete.Scatter
