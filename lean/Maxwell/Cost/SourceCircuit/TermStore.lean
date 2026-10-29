import Maxwell.Cost.SourceCircuit.LeafTransfer
import Maxwell.Cost.SourceCircuit.HornerTerm

/-! A fixed finite term compiler: transfer its preallocated leaves, emit the signed
Horner circuit, append its output identifier to the row stack, and clear the accumulator. -/

namespace Maxwell.Cost.SourceCircuit.TermStore
open Structured
open RationalAccumulator (Blank)

def result (negative : Bool) (bits next gates : List Bool) (leaves : List (List Bool)) : HornerLoop.Data :=
  HornerTerm.signed negative (bits.foldr HornerLoop.step (HornerTerm.initial next gates leaves))

def code : Code := .seq LeafTransfer.code
  (.seq HornerTerm.code (.seq (appendCode 94 104) (.call (TapeOps.clear 94))))

def program : BitRAM := code.compile

def costBound (precision width : ℕ) : ℕ := precision*(158*width+222)+112*width+187

def work : Finset ℕ := {83,94,95,96,97,98,99,103,104}

structure Frame (s t : Store) : Prop where
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  memory : t.val.memory = s.val.memory
  sign : t.val.registers 23 = s.val.registers 23
  tapes : ∀ j, (j = 4 ∨ 10 ≤ j) → j ∉ work → t.val.tapes j = s.val.tapes j
  control : ∀ j, 32 ≤ j → t.val.registers j = s.val.registers j

theorem Frame.trans {s t u : Store} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    k.memory.trans h.memory,k.sign.trans h.sign,
    fun j hj hn => (k.tapes j hj hn).trans (h.tapes j hj hn),
    fun j hj => (k.control j hj).trans (h.control j hj)⟩

theorem frame_leaf {s t : Store} (h : LeafTransfer.Frame s t) : Frame s t := by
  refine ⟨h.inputHead,h.randomCursor,h.output,h.memory,h.sign,?_,h.control⟩
  intro j _ hj
  exact h.tapes j (by
    intro he
    apply hj
    simp only [LeafTransfer.work,Finset.mem_insert,Finset.mem_singleton] at he
    simp only [work,Finset.mem_insert,Finset.mem_singleton]
    tauto)


theorem frame_horner {s t : Store} (h : HornerLoop.LoopFrame s t) : Frame s t := by
  refine ⟨h.inputHead,h.randomCursor,h.output,h.memory,h.sign,?_,h.control⟩
  intro j hj hn
  apply h.tapes j hj
  intro he
  exact hn (by
    simp only [HornerLoop.work,HornerStep.work,Finset.mem_insert,Finset.mem_singleton] at he
    simp only [work,Finset.mem_insert,Finset.mem_singleton]
    tauto)

theorem frame_common {s t : Store} (h : SourceCircuit.Frame work s.val t.val)
    (hm : t.val.memory = s.val.memory) : Frame s t :=
  ⟨h.inputHead,h.randomCursor,h.output,hm,h.sign,h.tapes,fun j hj => h.control j (by omega)⟩

structure Done (clock : List Bool) (d : HornerLoop.Data) (terms : List (List Bool)) (s : Store) : Prop where
  scratch : BankArray.Scratch s.val
  blank94 : Blank s.val 94
  blank96 : Blank s.val 96
  blank99 : Blank s.val 99
  blank103 : s.val.tapes 103 = BitTape.blank
  next : BankArray.Word s.val 95 d.next
  gates : s.val.tapes 97 = BitTape.atEnd d.gates
  terms : s.val.tapes 104 = BitTape.atEnd (terms ++ [d.accumulator]).flatten
  clock : BankArray.Word s.val 93 clock

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem executes (input : List Bool) (tape : ℕ → Bool) (width : ℕ)
    (clock bits next gates beforeAll suffix : List Bool) (leaves terms : List (List Bool))
    (negative : Bool) (origin : ℤ) (s : Store)
    (hclock : clock.length = width) (hlen : next.length = width)
    (hcount : leaves.length = bits.count true) (hleaves : ∀ word ∈ leaves, word.length = width)
    (hroom : addressValue next + 1 + bits.length + bits.count true + negative.toNat < 2^width)
    (hs : BankArray.Scratch s.val) (h94 : Blank s.val 94) (h96 : Blank s.val 96)
    (h99 : Blank s.val 99) (hn : BankArray.Word s.val 95 next)
    (hg : s.val.tapes 97 = BitTape.atEnd gates) (hc : BankArray.Word s.val 93 clock)
    (hl : s.val.tapes 103 = BitTape.blank)
    (hsource : s.val.tapes 98 = Increment.cursor beforeAll (leaves.flatten ++ suffix) 0)
    (hterms : s.val.tapes 104 = BitTape.atEnd terms.flatten)
    (hsign : s.val.registers 23 = negative)
    (hb : s.val.tapes 83 = BitTape.shifted bits origin) :
    ∃ cost t, cost ≤ costBound bits.length width ∧ Executes input tape code cost s t ∧
      Done clock (result negative bits next gates leaves) terms t ∧
      HornerLoop.Valid width [] (result negative bits next gates leaves) ∧
      t.val.tapes 83 = BitTape.shifted bits origin ∧
      t.val.tapes 98 = Increment.cursor (beforeAll ++ leaves.flatten) suffix 0 ∧ Frame s t := by
  obtain ⟨lc,l,hlc,el,l98,l103,l83,lf⟩ := LeafTransfer.executes input tape width bits beforeAll
    suffix clock leaves origin s hclock hcount hleaves hsource hl hc hb
  have keep := lf.tapes
  obtain ⟨ac,a,hac,ea,ar,av,a83,af⟩ := HornerTerm.executes input tape width clock bits next gates
    leaves negative origin l hclock hlen hcount hleaves hroom
    (scratch_of_tapes hs (fun j hj => keep j (by simp [LeafTransfer.work]; omega)))
    (RationalAccumulator.blank_of_eq (keep 94 (by decide)) h94)
    (RationalAccumulator.blank_of_eq (keep 96 (by decide)) h96)
    (RationalAccumulator.blank_of_eq (keep 99 (by decide)) h99)
    (BankArray.word_of_eq (keep 95 (by decide)) hn)
    ((keep 97 (by decide)).trans hg) l103
    (BankArray.word_of_eq (keep 93 (by decide)) hc) (lf.sign.trans hsign) l83
  let d := result negative bits next gates leaves
  change HornerLoop.Ready clock d a at ar
  change HornerLoop.Valid width [] d at av
  obtain ⟨accOrigin,accum⟩ := ar.accumulator
  obtain ⟨p,ep,pt,pf⟩ := append_executes 94 104 (by omega) input tape d.accumulator
    terms.flatten accOrigin a accum
    ((af.tapes 104 (by omega) (by decide)).trans ((keep 104 (by decide)).trans hterms))
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 94 input tape d.accumulator accOrigin p
    (by simpa [pt] using accum)
  have empty : d.leaves = [] := by simpa using av.leavesCount
  have frameP : SourceCircuit.Frame work a.val p.val := frame_transfer pf (by
    intro j hj
    have hn : j ≠ 104 := by intro he; exact hj (by simp [work,he])
    simp [pt,hn])
  have frameT : SourceCircuit.Frame work p.val t.val := frame_transfer (WordTransfer.frame_of_copy tf) (by
    intro j hj
    have hn : j ≠ 94 := by intro he; exact hj (by simp [work,he])
    simp [tt,hn])
  refine ⟨_,t,?_,el.seq (ea.seq (ep.seq et)),?_,av,
    by simpa [tt,pt] using a83,?_,
    (frame_leaf lf).trans ((frame_horner af).trans
      ((frame_common frameP pf.2.2.1).trans (frame_common frameT tf.2.2.1)))⟩
  · rw [av.accumulatorLength]
    simp only [costBound]
    nlinarith
  · refine ⟨scratch_of_tapes ar.scratch (by
      intro j hj
      simp [tt,pt,show j ≠ 94 by omega,show j ≠ 104 by omega]),
      ⟨accOrigin+d.accumulator.length,by simp [tt]⟩,
      RationalAccumulator.blank_of_eq (by simp [tt,pt]) ar.blank96,
      RationalAccumulator.blank_of_eq (by simp [tt,pt]) ar.blank99,
      (by simpa [tt,pt,empty,BitTape.atEnd_nil] using ar.leaves),
      BankArray.word_of_eq (by simp [tt,pt]) ar.next,
      (by simpa [tt,pt] using ar.gates),
      (by simp [tt,pt,d]),BankArray.word_of_eq (by simp [tt,pt]) ar.clock⟩
  · simpa [tt,pt] using (af.tapes 98 (by omega) (by decide)).trans l98

theorem run (input : List Bool) (tape : ℕ → Bool) (width : ℕ)
    (clock bits next gates beforeAll suffix : List Bool) (leaves terms : List (List Bool))
    (negative : Bool) (origin : ℤ) (s : Store)
    (hclock : clock.length = width) (hlen : next.length = width)
    (hcount : leaves.length = bits.count true) (hleaves : ∀ word ∈ leaves, word.length = width)
    (hroom : addressValue next + 1 + bits.length + bits.count true + negative.toNat < 2^width)
    (hs : BankArray.Scratch s.val) (h94 : Blank s.val 94) (h96 : Blank s.val 96)
    (h99 : Blank s.val 99) (hn : BankArray.Word s.val 95 next)
    (hg : s.val.tapes 97 = BitTape.atEnd gates) (hc : BankArray.Word s.val 93 clock)
    (hl : s.val.tapes 103 = BitTape.blank)
    (hsource : s.val.tapes 98 = Increment.cursor beforeAll (leaves.flatten ++ suffix) 0)
    (hterms : s.val.tapes 104 = BitTape.atEnd terms.flatten)
    (hsign : s.val.registers 23 = negative)
    (hb : s.val.tapes 83 = BitTape.shifted bits origin) :
    ∃ cost t,
      (runPriced (program.next input tape) (costBound bits.length width+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (program.next input tape) (costBound bits.length width+1) s.val).instructions = cost ∧
      cost ≤ costBound bits.length width ∧
      Done clock (result negative bits next gates leaves) terms t ∧
      HornerLoop.Valid width [] (result negative bits next gates leaves) ∧
      t.val.tapes 83 = BitTape.shifted bits origin ∧
      t.val.tapes 98 = Increment.cursor (beforeAll ++ leaves.flatten) suffix 0 ∧ Frame s t := by
  obtain ⟨cost,t,hcost,he,hd,hv,h83,h98,hf⟩ := executes input tape width clock bits next gates
    beforeAll suffix leaves terms negative origin s hclock hlen hcount hleaves hroom hs h94 h96 h99
    hn hg hc hl hsource hterms hsign hb
  obtain ⟨finished,charged⟩ := he.compiled_run (costBound bits.length width+1) (by omega)
  exact ⟨cost,t,finished,charged,hcost,hd,hv,h83,h98,hf⟩

end Maxwell.Cost.SourceCircuit.TermStore
