import Maxwell.Cost.SourceCircuit.RowSumData

namespace Maxwell.Cost.SourceCircuit.RowSum
open Structured
open RationalAccumulator (Blank)

def body : Code := .seq (WordStack.code 104 93 99)
  (.seq HornerStep.addLeaf (.call (TapeOps.clear 99)))

def code : Code := CountedShifted.code 106 body
def program : BitRAM := code.compile

def costBound (count width counterWidth : ℕ) : ℕ :=
  (count+1) * (13*counterWidth+15) + count * (88*width+104)

set_option maxRecDepth 8192 in
theorem body_executes (input : List Bool) (tape : ℕ → Bool) (clock : List Bool)
    (width count : ℕ) (d : Data) (s : Store) (hc : clock.length = width)
    (ready : Ready clock d s) (valid : Valid width (count+1) d) :
    ∃ cost, ∃ t : Store, cost ≤ 88*width+104 ∧ Executes input tape body cost s t ∧
      Ready clock (step d) t ∧ t.val.memory = s.val.memory ∧ Frame bodyWork s.val t.val := by
  obtain ⟨hne, leafLength, decomp⟩ := last_word valid
  obtain ⟨targetOrigin, ht⟩ := ready.blank99
  obtain ⟨clockOrigin, hclock⟩ := ready.clock
  have stack : s.val.tapes 104 = BitTape.atEnd
      (d.terms.dropLast.flatten ++ d.terms.getLastD []) := by
    rw [ready.terms, ← decomp]
    simp
  obtain ⟨p, ep, pl, p99, _, _, pm, pf, pk⟩ := WordStack.executes 104 93 99
    (by omega) (by omega) (by omega) input tape (d.terms.getLastD []) d.terms.dropLast.flatten
    clock targetOrigin clockOrigin s (hc.trans leafLength.symm) stack ht hclock
  have ps := scratch_of_tapes ready.scratch (fun j hj => pk j (by omega) (by omega))
  obtain ⟨ac, a, hac, ea, an, aa, a96, ag, am, ascratch, af⟩ := HornerStep.addLeaf_executes
    input tape d.next d.accumulator (d.terms.getLastD []) d.gates p ps
    (RationalAccumulator.blank_of_eq (pk 96 (by omega) (by omega)) ready.blank96)
    (BankArray.word_of_eq (pk 95 (by omega) (by omega)) ready.next)
    (BankArray.word_of_eq (pk 94 (by omega) (by omega)) ready.accumulator)
    ⟨targetOrigin-(d.terms.getLastD []).length, p99⟩
    ((pk 97 (by omega) (by omega)).trans ready.gates)
    (valid.accumulatorLength.trans valid.nextLength.symm)
    (leafLength.trans valid.nextLength.symm)
  have a99 : a.val.tapes 99 = BitTape.shifted (d.terms.getLastD [])
      (targetOrigin-(d.terms.getLastD []).length) :=
    (af.tapes 99 (by omega) (by simp [accumulatorWork])).trans p99
  obtain ⟨t, et, tt, tf⟩ := WordCall.clear 99 input tape (d.terms.getLastD [])
    (targetOrigin-(d.terms.getLastD []).length) a a99
  have pframe : Frame bodyWork s.val p.val := pf.mono (by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp [bodyWork])
  have aframe : Frame bodyWork p.val a.val := af.mono (by simp [accumulatorWork, bodyWork])
  have tframe : Frame bodyWork a.val t.val := frame_transfer (WordTransfer.frame_of_copy tf) (by
    intro j hj
    have j99 : j ≠ 99 := by intro he; exact hj (by simp [bodyWork, he])
    simp [tt, j99])
  have frame := pframe.trans (aframe.trans tframe)
  refine ⟨_, t, ?_, ep.seq (ea.seq et), ?_, tf.2.2.1.trans (am.trans pm), frame⟩
  · rw [valid.nextLength] at hac
    omega
  · refine ⟨scratch_of_tapes ascratch (by intro j hj; simp [tt, show j ≠ 99 by omega]),
      RationalAccumulator.blank_of_eq (by simp [tt]) a96,
      ⟨targetOrigin-(d.terms.getLastD []).length+(d.terms.getLastD []).length, by simp [tt]⟩,
      BankArray.word_of_eq (by simp [tt]) an,
      BankArray.word_of_eq (by simp [tt]) aa,
      (by simpa [tt, step] using ag), ?_,
      BankArray.word_of_eq (frame.tapes 93 (by omega) (by simp [bodyWork])) ready.clock⟩
    change t.val.tapes 104 = BitTape.atEnd d.terms.dropLast.flatten
    rw [tt]
    simpa using (af.tapes 104 (by omega) (by simp [accumulatorWork])).trans pl

set_option maxRecDepth 8192 in
theorem executes (input : List Bool) (tape : ℕ → Bool) (clock counter : List Bool)
    (width : ℕ) (counterOrigin : ℤ) (d : Data) (s : Store)
    (hc : clock.length = width) (hcount : addressValue counter = d.terms.length)
    (hcounter : s.val.tapes 106 = BitTape.shifted counter counterOrigin)
    (ready : Ready clock d s) (valid : Valid width d.terms.length d) :
    ∃ cost, ∃ t : Store, ∃ finalCounter : List Bool,
      cost ≤ costBound d.terms.length width counter.length ∧ Executes input tape code cost s t ∧
      Ready clock (complete d) t ∧ Valid width 0 (complete d) ∧
      t.val.tapes 106 = BitTape.shifted finalCounter counterOrigin ∧
      finalCounter.length = counter.length ∧ t.val.memory = s.val.memory ∧ Frame work s.val t.val := by
  let inv : ℕ → Store → Prop := fun remaining u => ∃ current : Data,
    Ready clock current u ∧ Valid width remaining current ∧ complete current = complete d ∧
      u.val.memory = s.val.memory ∧ Frame work s.val u.val
  have stable : ∀ n u v, Counted.Frame 106 u v → inv n u → inv n v := by
    rintro n u v hf ⟨current, hr, hv, he, hm, frame⟩
    exact ⟨current, hr.count hf, hv, he, hf.2.2.1.trans hm, frame.trans (count_frame hf)⟩
  have correct : ∀ n xs u, inv (n+1) u →
      u.val.tapes 106 = BitTape.shifted xs counterOrigin → addressValue xs = n →
      ∃ cost v, Executes input tape body cost u v ∧ inv n v ∧
        v.val.tapes 106 = BitTape.shifted xs counterOrigin ∧ cost ≤ 88*width+104 := by
    rintro n xs u ⟨current, hr, hv, he, hm, frame⟩ hu _
    obtain ⟨cost, v, hcost, ev, vr, vm, vf⟩ := body_executes input tape clock width n current u hc hr hv
    have hne : current.terms ≠ [] := (last_word hv).1
    refine ⟨cost, v, ev, ⟨step current, vr, valid_step hv,
      (complete_step current hne).trans he, vm.trans hm,
      frame.trans (vf.mono (by simp [bodyWork, work]))⟩,
      (vf.tapes 106 (by omega) (by simp [bodyWork])).trans hu, hcost⟩
  obtain ⟨cost, t, finalCounter, execution, hi, ht, hlen, _, hcost⟩ :=
    CountedShifted.executes 106 counterOrigin body input tape inv (fun _ => 88*width+104)
      stable correct d.terms.length counter s hcount hcounter
      ⟨d, ready, valid, rfl, rfl, ⟨rfl, rfl, rfl, fun _ _ _ => rfl, rfl, fun _ _ => rfl⟩⟩
  obtain ⟨current, hr, hv, he, hm, frame⟩ := hi
  have empty : current.terms = [] := by simpa using hv.termsCount
  have eq : current = complete d := (complete_empty empty).symm.trans he
  refine ⟨cost, t, finalCounter, ?_, execution, eq ▸ hr, eq ▸ hv, ht, hlen, hm, frame⟩
  simpa [costBound] using hcost

theorem run (input : List Bool) (tape : ℕ → Bool) (clock counter : List Bool)
    (width : ℕ) (counterOrigin : ℤ) (d : Data) (s : Store)
    (hc : clock.length = width) (hcount : addressValue counter = d.terms.length)
    (hcounter : s.val.tapes 106 = BitTape.shifted counter counterOrigin)
    (ready : Ready clock d s) (valid : Valid width d.terms.length d) :
    ∃ cost, ∃ t : Store,
      (runPriced (program.next input tape) (costBound d.terms.length width counter.length+1)
        s.val).finished = some (t.place code.size) ∧
      (runPriced (program.next input tape) (costBound d.terms.length width counter.length+1)
        s.val).instructions = cost ∧ cost ≤ costBound d.terms.length width counter.length ∧
      Ready clock (complete d) t ∧ Valid width 0 (complete d) ∧
      t.val.memory = s.val.memory ∧ Frame work s.val t.val := by
  obtain ⟨cost, t, _, hcost, he, hr, hv, _, _, hm, hf⟩ := executes input tape clock counter
    width counterOrigin d s hc hcount hcounter ready valid
  obtain ⟨finished, charged⟩ := he.compiled_run (costBound d.terms.length width counter.length+1) (by omega)
  exact ⟨cost, t, finished, charged, hcost, hr, hv, hm, hf⟩

def outputCode : Code := .seq code
  (.seq (appendCode 94 105) (.call (TapeOps.clear 94)))

def outputWork : Finset ℕ := insert 105 work

structure Done (clock : List Bool) (d : Data) (outputs : List Bool) (s : Store) : Prop where
  scratch : BankArray.Scratch s.val
  blank94 : Blank s.val 94
  blank96 : Blank s.val 96
  blank99 : Blank s.val 99
  next : BankArray.Word s.val 95 d.next
  gates : s.val.tapes 97 = BitTape.atEnd d.gates
  terms : s.val.tapes 104 = BitTape.atEnd []
  clock : BankArray.Word s.val 93 clock
  outputs : s.val.tapes 105 = BitTape.atEnd (outputs ++ d.accumulator)

theorem output_executes (input : List Bool) (tape : ℕ → Bool) (clock counter outputs : List Bool)
    (width : ℕ) (counterOrigin : ℤ) (d : Data) (s : Store)
    (hc : clock.length = width) (hcount : addressValue counter = d.terms.length)
    (hcounter : s.val.tapes 106 = BitTape.shifted counter counterOrigin)
    (hout : s.val.tapes 105 = BitTape.atEnd outputs)
    (ready : Ready clock d s) (valid : Valid width d.terms.length d) :
    ∃ cost, ∃ t : Store,
      cost ≤ costBound d.terms.length width counter.length + 17*width+14 ∧
      Executes input tape outputCode cost s t ∧ Done clock (complete d) outputs t ∧
      Valid width 0 (complete d) ∧ t.val.memory = s.val.memory ∧ Frame outputWork s.val t.val ∧
      ∃ finalCounter, t.val.tapes 106 = BitTape.shifted finalCounter counterOrigin ∧
        finalCounter.length = counter.length := by
  obtain ⟨cost, a, finalCounter, hcost, ea, ar, av, aCounter, counterLength, am, af⟩ := executes input tape clock counter
    width counterOrigin d s hc hcount hcounter ready valid
  obtain ⟨origin, accum⟩ := ar.accumulator
  obtain ⟨p, ep, pt, pf⟩ := append_executes 94 105 (by omega) input tape
    (complete d).accumulator outputs origin a accum
    ((af.tapes 105 (by omega) (by simp [work])).trans hout)
  obtain ⟨t, et, tt, tf⟩ := WordCall.clear 94 input tape (complete d).accumulator origin p
    (by simpa [pt] using accum)
  have empty : (complete d).terms = [] := by simpa using av.termsCount
  have frameP : Frame outputWork a.val p.val := frame_transfer pf (by
    intro j hj
    have hn : j ≠ 105 := by intro he; exact hj (by simp [outputWork, he])
    simp [pt, hn])
  have frameT : Frame outputWork p.val t.val := frame_transfer (WordTransfer.frame_of_copy tf) (by
    intro j hj
    have hn : j ≠ 94 := by intro he; exact hj (by simp [outputWork, work, he])
    simp [tt, hn])
  refine ⟨_, t, ?_, ea.seq (ep.seq et), ?_, av, tf.2.2.1.trans (pf.2.2.1.trans am),
    (af.mono (by simp [outputWork])).trans (frameP.trans frameT),
    finalCounter,by simpa [tt,pt] using aCounter,counterLength⟩
  · rw [av.accumulatorLength]
    omega
  · refine ⟨scratch_of_tapes ar.scratch (by
      intro j hj
      simp [tt, pt, show j ≠ 94 by omega, show j ≠ 105 by omega]),
      ⟨origin+(complete d).accumulator.length, by simp [tt]⟩,
      RationalAccumulator.blank_of_eq (by simp [tt, pt]) ar.blank96,
      RationalAccumulator.blank_of_eq (by simp [tt, pt]) ar.blank99,
      BankArray.word_of_eq (by simp [tt, pt]) ar.next,
      (by simpa [tt, pt] using ar.gates),
      (by simpa [tt, pt, empty] using ar.terms),
      BankArray.word_of_eq (by simp [tt, pt]) ar.clock,
      (by simp [tt, pt])⟩

end Maxwell.Cost.SourceCircuit.RowSum
