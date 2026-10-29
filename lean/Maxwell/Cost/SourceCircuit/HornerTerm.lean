import Maxwell.Cost.SourceCircuit.HornerLoop
import Maxwell.Cost.SourceCircuit.HornerTermData
import Maxwell.Cost.SourceCircuit.SeekEnd

namespace Maxwell.Cost.SourceCircuit.HornerTerm
open Structured
open RationalAccumulator (Blank)
open HornerLoop

def zeroCode : Code := emitAccumulatorCode zeroTag []
def signCode : Code := .branch 23 (emitAccumulatorCode negativeTag [94]) .skip
def code : Code := .seq zeroCode (.seq (SeekEnd.code 83) (.seq HornerLoop.code signCode))

theorem zero_executes (input : List Bool) (tape : ℕ → Bool) (next gates clock : List Bool)
    (leaves : List (List Bool)) (s : Store) (hs : BankArray.Scratch s.val)
    (h94 : Blank s.val 94) (h96 : Blank s.val 96) (h99 : Blank s.val 99)
    (hn : BankArray.Word s.val 95 next) (hg : s.val.tapes 97 = BitTape.atEnd gates)
    (hl : s.val.tapes 103 = BitTape.atEnd leaves.flatten) (hc : BankArray.Word s.val 93 clock) :
    ∃ cost t, cost ≤ 39*next.length+70 ∧ Executes input tape zeroCode cost s t ∧
      Ready clock (initial next gates leaves) t ∧ t.val.memory = s.val.memory ∧
      Frame accumulatorWork s.val t.val := by
  have empty : BankArray.Word s.val 94 [] := by
    obtain ⟨origin,he⟩ := h94
    exact ⟨origin,by simpa using he⟩
  obtain ⟨cost,t,hcost,he,tn,ta,t96,tg,tm,ts,tf⟩ :=
    emitAccumulator_executes input tape zeroTag next [] gates [] s hs h96 hn empty
      (by simp) hg
  refine ⟨cost,t,?_,he,⟨ts,t96,
    RationalAccumulator.blank_of_eq (tf.tapes 99 (by omega) (by simp [accumulatorWork])) h99,
    tn,ta,by simpa [initial] using tg,
    (tf.tapes 103 (by omega) (by simp [accumulatorWork])).trans hl,
    BankArray.word_of_eq (tf.tapes 93 (by omega) (by simp [accumulatorWork])) hc⟩,tm,tf⟩
  simpa [zeroTag,fieldCost] using hcost

theorem sign_executes (input : List Bool) (tape : ℕ → Bool) (negative : Bool)
    (clock : List Bool) (d : Data) (s : Store) (hr : Ready clock d s)
    (hlen : d.accumulator.length = d.next.length) (hsign : s.val.registers 23 = negative) :
    ∃ cost t, cost ≤ 56*d.next.length+81 ∧ Executes input tape signCode cost s t ∧
      Ready clock (signed negative d) t ∧ t.val.memory = s.val.memory ∧
      Frame accumulatorWork s.val t.val := by
  cases negative with
  | false =>
    exact ⟨2,s,by omega,.no hsign (.skip s),hr,rfl,
      ⟨rfl,rfl,rfl,fun _ _ _ => rfl,rfl,fun _ _ => rfl⟩⟩
  | true =>
    obtain ⟨cost,t,hcost,he,tn,ta,t96,tg,tm,ts,tf⟩ :=
      emitAccumulator_executes input tape negativeTag d.next d.accumulator d.gates
        [(94,d.accumulator)] s hr.scratch hr.blank96 hr.next hr.accumulator
        (by intro field hf; simp only [List.mem_singleton] at hf; subst field
            exact ⟨by omega,by omega,hr.accumulator⟩) hr.gates
    refine ⟨1+cost,t,?_,.yes hsign he,⟨ts,t96,
      RationalAccumulator.blank_of_eq (tf.tapes 99 (by omega) (by simp [accumulatorWork])) hr.blank99,
      tn,ta,by simpa [signed] using tg,
      (tf.tapes 103 (by omega) (by simp [accumulatorWork])).trans hr.leaves,
      BankArray.word_of_eq (tf.tapes 93 (by omega) (by simp [accumulatorWork])) hr.clock⟩,tm,tf⟩
    simp only [negativeTag,List.length_cons,List.length_nil,fieldCost,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,hlen] at hcost
    omega

theorem frame_accumulator {s t : Store} (h : Frame accumulatorWork s.val t.val)
    (hm : t.val.memory = s.val.memory) : LoopFrame s t :=
  loopFrame_step (h.mono (by simp [accumulatorWork,HornerStep.work])) hm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem executes (input : List Bool) (tape : ℕ → Bool) (width : ℕ)
    (clock bits next gates : List Bool) (leaves : List (List Bool))
    (negative : Bool) (origin : ℤ) (s : Store)
    (hclock : clock.length = width) (hlen : next.length = width)
    (hcount : leaves.length = bits.count true) (hleaves : ∀ word ∈ leaves, word.length = width)
    (hroom : addressValue next + 1 + bits.length + bits.count true + negative.toNat < 2^width)
    (hs : BankArray.Scratch s.val) (h94 : Blank s.val 94) (h96 : Blank s.val 96)
    (h99 : Blank s.val 99) (hn : BankArray.Word s.val 95 next)
    (hg : s.val.tapes 97 = BitTape.atEnd gates)
    (hl : s.val.tapes 103 = BitTape.atEnd leaves.flatten)
    (hc : BankArray.Word s.val 93 clock) (hsign : s.val.registers 23 = negative)
    (hb : s.val.tapes 83 = BitTape.shifted bits origin) :
    ∃ cost t, cost ≤ bits.length*(144*width+200)+95*width+163 ∧
      Executes input tape code cost s t ∧
      Ready clock (signed negative (bits.foldr step (initial next gates leaves))) t ∧
      Valid width [] (signed negative (bits.foldr step (initial next gates leaves))) ∧
      t.val.tapes 83 = BitTape.shifted bits origin ∧ LoopFrame s t := by
  obtain ⟨zc,z,hzc,ez,zr,zm,zf⟩ := zero_executes input tape next gates clock leaves s
    hs h94 h96 h99 hn hg hl hc
  obtain ⟨sc,a,hsc,ea,ab,af⟩ := SeekEnd.executes 83 input tape bits origin z
    ((zf.tapes 83 (by omega) (by simp [accumulatorWork])).trans hb)
  have iv := initial_valid width bits next gates leaves hlen hcount hleaves (by omega)
  obtain ⟨lc,l,hlc,el,lr,lv,lb,lf⟩ := HornerLoop.executes input tape width clock bits origin
    (initial next gates leaves) a hclock (zr.passive af) iv ab
  obtain ⟨nc,t,hnc,et,tr,tm,tf⟩ := sign_executes input tape negative clock _ l lr
    (lv.accumulatorLength.trans lv.nextLength.symm)
    (lf.sign.trans ((af.registers 23 (by omega) (by omega)).trans (zf.sign.trans hsign)))
  have room : addressValue (bits.foldr step (initial next gates leaves)).next + negative.toNat < 2^width := by
    rw [fold_next]
    simpa [initial,Increment.bits_value] using hroom
  refine ⟨zc+(sc+(lc+nc)),t,?_,ez.seq (ea.seq (el.seq et)),tr,
    signed_valid width negative _ lv room,
    (tf.tapes 83 (by omega) (by simp [accumulatorWork])).trans lb,
    (frame_accumulator zf zm).trans ((loopFrame_passive af).trans
      (lf.trans (frame_accumulator tf tm)))⟩
  rw [hlen] at hzc
  rw [lv.nextLength] at hnc
  nlinarith

end Maxwell.Cost.SourceCircuit.HornerTerm
