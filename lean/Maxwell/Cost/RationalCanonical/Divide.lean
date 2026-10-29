import Maxwell.Cost.Division
import Maxwell.Cost.NormalizeWord
import Maxwell.Cost.WordCall
import Maxwell.Cost.BankArray.Common

namespace Maxwell.Cost.RationalCanonical

open Structured
open RationalAccumulator (Blank)

/-- Preservation for the concrete division wrapper and its constituent calls. -/
structure DivisionFrame (changed : Finset ℕ) (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ changed → t.tapes i = s.tapes i
  registers : ∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 →
    t.registers i = s.registers i

theorem DivisionFrame.trans {a b : Finset ℕ} {s t u : BitRAMState}
    (h : DivisionFrame a s t) (k : DivisionFrame b t u) : DivisionFrame (a ∪ b) s u :=
  ⟨k.address.trans h.address, k.memory.trans h.memory, k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i hi => (k.tapes i (fun hb => hi (Finset.mem_union_right a hb))).trans
      (h.tapes i (fun ha => hi (Finset.mem_union_left b ha))),
    fun i hi h24 h25 h26 h27 => (k.registers i hi h24 h25 h26 h27).trans
      (h.registers i hi h24 h25 h26 h27)⟩

theorem DivisionFrame.mono {a b : Finset ℕ} {s t : BitRAMState}
    (h : DivisionFrame a s t) (hab : a ⊆ b) : DivisionFrame b s t :=
  {h with tapes := fun i hi => h.tapes i (fun ha => hi (hab ha))}

theorem DivisionFrame.word {changed : Finset ℕ} {s t : BitRAMState}
    (h : DivisionFrame changed s t) {i : ℕ} (hi : i ∉ changed) {word : List Bool}
    (hw : BankArray.Word s i word) : BankArray.Word t i word :=
  BankArray.word_of_eq (h.tapes i hi) hw

theorem DivisionFrame.blank {changed : Finset ℕ} {s t : BitRAMState}
    (h : DivisionFrame changed s t) {i : ℕ} (hi : i ∉ changed)
    (hw : Blank s i) : Blank t i := RationalAccumulator.blank_of_eq (h.tapes i hi) hw

private theorem DivisionFrame.reset_right {changed : Finset ℕ} {s t : BitRAMState}
    (h : DivisionFrame changed s t) : DivisionFrame changed s (Store.ofState t).val :=
  ⟨h.address, h.memory, h.inputHead, h.randomCursor, h.output, h.tapes, h.registers⟩

private theorem transfer_frame (source target : ℕ) {s t : BitRAMState}
    (h : WordTransfer.Frame source target s t) : DivisionFrame {source, target} s t :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi => h.2.2.2.2.2.1 i (by intro he; subst i; simp at hi)
      (by intro he; subst i; simp at hi),
    fun i _ h24 h25 h26 h27 => h.2.2.2.2.2.2 i h24 h25 h26 h27⟩

private theorem clone_word (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (word : List Bool) (s : Store)
    (hw : BankArray.Word s.val source word) (hb : Blank s.val target) :
    ∃ t, Executes input tape (.call (WordTransfer.clone source target))
      (15*word.length+17) s t ∧ BankArray.Word t.val target word ∧
      DivisionFrame {target} s.val t.val := by
  obtain ⟨so, hs⟩ := hw
  obtain ⟨targetOrigin, ht⟩ := hb
  obtain ⟨t, he, htapes, hf⟩ := WordCall.clone source target hne input tape word so targetOrigin s hs ht
  refine ⟨t, he, ⟨targetOrigin, by simp [htapes]⟩,
    ⟨hf.1, hf.2.2.1, hf.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_, ?_⟩⟩
  · intro i hi
    have hit : i ≠ target := by simpa using hi
    simp [htapes, hit]
  · intro i _ h24 h25 h26 h27
    exact hf.2.2.2.2.2.2 i h24 h25 h26 h27

private theorem clear_word (target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (word : List Bool) (s : Store) (hw : BankArray.Word s.val target word) :
    ∃ t, Executes input tape (.call (TapeOps.clear target)) (6*word.length+4) s t ∧
      Blank t.val target ∧ DivisionFrame {target} s.val t.val := by
  obtain ⟨origin, hw⟩ := hw
  obtain ⟨t, he, ht, hf⟩ := WordCall.clear target input tape word origin s hw
  refine ⟨t, he, ⟨origin+word.length, by simp [ht]⟩, ?_⟩
  simpa using transfer_frame target target (WordTransfer.frame_of_copy hf)

private theorem forward_word (target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (word : List Bool) (s : Store) (hw : BankArray.Word s.val target word) :
    ∃ t origin, Executes input tape (.call (ScanForward.program target))
      (5*word.length+4) s t ∧ t.val.tapes target = BitTape.shiftedEnd word origin ∧
      DivisionFrame {target} s.val t.val := by
  obtain ⟨origin, hw⟩ := hw
  obtain ⟨he, ht, hf⟩ := ScanForward.shifted_steps target origin input tape word s.val s.property hw
  refine ⟨Store.ofState (ScanForward.finish target word.length s.val), origin,
    .call _ _ _ _ he (by simp [ScanForward.program, ScanForward.finish]), ht, ?_⟩
  simpa using (transfer_frame target target (WordTransfer.frame_of_copy hf)).reset_right

private def exportCode (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.move source target)) (.call (NormalizeWord.program target))

private theorem export_word (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (word : List Bool) (s : Store)
    (hw : BankArray.Word s.val source word) (hb : Blank s.val target) :
    ∃ cost t, cost ≤ 28*word.length+29 ∧ Executes input tape (exportCode source target) cost s t ∧
      RationalAccumulator.Word t.val target (addressValue word) ∧ Blank t.val source ∧
      DivisionFrame {source, target} s.val t.val := by
  obtain ⟨so, hs⟩ := hw
  obtain ⟨targetOrigin, ht⟩ := hb
  obtain ⟨a, ea, pa, has, hat, haf⟩ := WordTransfer.move_steps source target hne input tape
    word so targetOrigin s.val s.property hs ht
  have em : Executes input tape (.call (WordTransfer.move source target))
      (12*word.length+11) s (Store.ofState a) := .call _ _ _ _ ea (by rw [pa]; rfl)
  obtain ⟨cost, t, hcost, et, pt, htword, _, htf⟩ := NormalizeWord.simulation target targetOrigin input tape
    word (Store.ofState a).val (Store.ofState a).property hat
  have en : Executes input tape (.call (NormalizeWord.program target))
      (cost+1) (Store.ofState a) (Store.ofState t) := .call _ _ _ _ et (by rw [pt]; rfl)
  have nf : DivisionFrame {source, target} a t :=
    ⟨htf.1, htf.2.2.1, htf.2.1, htf.2.2.2.1, htf.2.2.2.2.1,
      fun i hi => htf.2.2.2.2.2.1 i (by intro he; subst i; simp at hi),
      fun i _ h24 h25 h26 h27 => htf.2.2.2.2.2.2 i h24 h25 h26 h27⟩
  refine ⟨12*word.length+11+(cost+1), Store.ofState t, by omega, em.seq en,
    ⟨targetOrigin, htword⟩, ⟨so+word.length, (htf.2.2.2.2.2.1 source hne).trans has⟩, ?_⟩
  simpa using ((transfer_frame source target haf).trans nf).reset_right

private def loadCode : Code :=
  .seq (.call (WordTransfer.clone 220 3))
    (.seq (.call (WordTransfer.clone 221 1)) (.call (ScanForward.program 3)))

private theorem load (input : List Bool) (tape : ℕ → Bool) (a b : ℕ) (s : Store)
    (ha : RationalAccumulator.Word s.val 220 a) (hb : RationalAccumulator.Word s.val 221 b)
    (hs : ∀ i, i < 5 → Blank s.val i) :
    ∃ t origin, Executes input tape loadCode (20*a.bits.length+15*b.bits.length+38) s t ∧
      BankArray.Word t.val 1 b.bits ∧ t.val.tapes 3 = BitTape.shiftedEnd a.bits origin ∧
      Blank t.val 0 ∧ Blank t.val 2 ∧ Blank t.val 4 ∧ DivisionFrame {1,3} s.val t.val := by
  obtain ⟨u, eu, hu, fu⟩ := clone_word 220 3 (by decide) input tape a.bits s ha (hs 3 (by omega))
  obtain ⟨v, ev, hv, fv⟩ := clone_word 221 1 (by decide) input tape b.bits u
    (fu.word (by decide) hb) (fu.blank (by decide) (hs 1 (by omega)))
  obtain ⟨t, origin, et, ht, ft⟩ := forward_word 3 input tape a.bits v (fv.word (by decide) hu)
  have frame : DivisionFrame {1,3} s.val t.val := by
    simpa [Finset.union_comm] using fu.trans (fv.trans ft)
  refine ⟨t, origin, ?_, ft.word (by decide) hv, ht,
    frame.blank (by decide) (hs 0 (by omega)),
    frame.blank (by decide) (hs 2 (by omega)),
    frame.blank (by decide) (hs 4 (by omega)), frame⟩
  convert eu.seq (ev.seq et) using 1 <;> first | rfl | omega

private def cleanupCode : Code :=
  .seq (exportCode 0 223) <|
  .seq (exportCode 4 222) <|
  .seq (.call (TapeOps.clear 1)) <|
  .seq (.atom (.tapeRight 3)) (.call (TapeOps.clear 3))

private theorem cleanup (input : List Bool) (tape : ℕ → Bool)
    (divisor dividend remainder quotient : List Bool) (origin : ℤ) (s : Store)
    (h0 : BankArray.Word s.val 0 remainder) (h1 : BankArray.Word s.val 1 divisor)
    (h2 : Blank s.val 2)
    (h3 : s.val.tapes 3 = {BitTape.shifted dividend origin with head := origin-1})
    (h4 : BankArray.Word s.val 4 quotient) (h222 : Blank s.val 222) (h223 : Blank s.val 223) :
    ∃ cost t, cost ≤ 28*remainder.length+28*quotient.length+
        6*divisor.length+6*dividend.length+68 ∧
      Executes input tape cleanupCode cost s t ∧
      RationalAccumulator.Word t.val 222 (addressValue quotient) ∧
      RationalAccumulator.Word t.val 223 (addressValue remainder) ∧
      (∀ i, i < 5 → Blank t.val i) ∧ DivisionFrame {0,1,3,4,222,223} s.val t.val := by
  obtain ⟨c1, s1, hc1, e1, w1, z1, f1⟩ := export_word 0 223 (by decide) input tape remainder s h0 h223
  obtain ⟨c2, s2, hc2, e2, w2, z2, f2⟩ := export_word 4 222 (by decide) input tape quotient s1
    (f1.word (by decide) h4) (f1.blank (by decide) h222)
  obtain ⟨s3, e3, z3, f3⟩ := clear_word 1 input tape divisor s2
    (f2.word (by decide) (f1.word (by decide) h1))
  let s4 := Store.ofState (s3.val.setTape 3 {s3.val.tapes 3 with head := (s3.val.tapes 3).head+1})
  have e4 : Executes input tape (.atom (.tapeRight 3)) 2 s3 s4 :=
    Executes.tapeRight input tape s3 3
  have f4 : DivisionFrame {3} s3.val s4.val := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ _ _ _ _ => rfl⟩
    intro i hi
    have hi3 : i ≠ 3 := by simpa using hi
    simp [s4, Store.ofState, BitRAMState.setTape, hi3]
  have w3 : BankArray.Word s4.val 3 dividend := by
    have h3s := (f3.tapes 3 (by decide)).trans
      ((f2.tapes 3 (by decide)).trans ((f1.tapes 3 (by decide)).trans h3))
    exact ⟨origin, by simp [s4, Store.ofState, BitRAMState.setTape, h3s, BitTape.shifted]⟩
  obtain ⟨t, e5, z5, f5⟩ := clear_word 3 input tape dividend s4 w3
  have frame : DivisionFrame {0,1,3,4,222,223} s.val t.val := by
    apply (f1.trans (f2.trans (f3.trans (f4.trans f5)))).mono
    intro i hi
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    tauto
  refine ⟨c1+(c2+((6*divisor.length+4)+(2+(6*dividend.length+4)))), t, by omega,
    e1.seq (e2.seq (e3.seq (e4.seq e5))),
    f5.word (by decide) (f4.word (by decide) (f3.word (by decide) w2)),
    f5.word (by decide) (f4.word (by decide) (f3.word (by decide)
      (f2.word (by decide) w1))), ?_, frame⟩
  intro i hi
  interval_cases i
  · exact f5.blank (by decide) (f4.blank (by decide) (f3.blank (by decide)
      (f2.blank (by decide) z1)))
  · exact f5.blank (by decide) (f4.blank (by decide) z3)
  · exact frame.blank (by decide) h2
  · exact z5
  · exact f5.blank (by decide) (f4.blank (by decide) (f3.blank (by decide) z2))

/-- Canonical natural division on banks 220/221, returning quotient/remainder
on 222/223. Every loop and cleanup operation is finite machine syntax. -/
def divideCode : Code := .seq loadCode (.seq (.call Division.program) cleanupCode)

/-- Actual zero-safe division, with canonical outputs and all five arithmetic
work tapes cleared. The input operands and every other bank are preserved. -/
theorem divide (input : List Bool) (tape : ℕ → Bool) (a b : ℕ) (hbpos : 0 < b)
    (s : Store) (ha : RationalAccumulator.Word s.val 220 a)
    (hb : RationalAccumulator.Word s.val 221 b)
    (hs : ∀ i, i < 5 → Blank s.val i) (h222 : Blank s.val 222) (h223 : Blank s.val 223) :
    ∃ cost t, cost ≤ 1000*(a.bits.length+b.bits.length+2)^2 ∧
      Executes input tape divideCode cost s t ∧
      RationalAccumulator.Word t.val 222 (a/b) ∧ RationalAccumulator.Word t.val 223 (a%b) ∧
      RationalAccumulator.Word t.val 220 a ∧ RationalAccumulator.Word t.val 221 b ∧
      (∀ i, i < 5 → Blank t.val i) ∧ DivisionFrame {0,1,2,3,4,222,223} s.val t.val := by
  obtain ⟨l, origin, el, hl1, hl3, hl0, hl2, hl4, fl⟩ := load input tape a b s ha hb hs
  obtain ⟨ao, h0⟩ := hl0
  obtain ⟨xo, h1⟩ := hl1
  obtain ⟨zo, h2⟩ := hl2
  obtain ⟨qo, h4⟩ := hl4
  obtain ⟨dc, d, remainder, quotient, ro, scratchOrigin, quotientOrigin,
      hdc, ed, pd, hd0, hd1, hd2, hd4, hrvalue, hqvalue, hrlen, hqlen, hd3⟩ :=
    Division.simulation_cleanup input tape l.val b.bits a.bits ao xo zo origin qo
      (by simpa using hbpos) l.property h0 h1 h2 hl3 h4
  have ecall : Executes input tape (.call Division.program) (dc+1) l (Store.ofState d) :=
    .call _ _ _ _ ed (by rw [pd]; rfl)
  have df := Division.execution_frame input tape ed
  have fd : DivisionFrame {0,1,2,3,4} l.val (Store.ofState d).val := by
    refine ⟨df.1, df.2.2.1, df.2.1, df.2.2.2.1, df.2.2.2.2.1, ?_, df.2.2.2.2.2.2.2.2⟩
    intro i hi
    apply df.2.2.2.2.2.2.2.1 i
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    omega
  obtain ⟨cc, t, hcc, ec, hq, hr, htready, fc⟩ := cleanup input tape b.bits a.bits
    remainder quotient origin (Store.ofState d) ⟨ro, hd0⟩ ⟨xo, hd1⟩ ⟨scratchOrigin, hd2⟩ hd3
    ⟨quotientOrigin, hd4⟩ (fd.blank (by decide) (fl.blank (by decide) h222))
    (fd.blank (by decide) (fl.blank (by decide) h223))
  have frame : DivisionFrame {0,1,2,3,4,222,223} s.val t.val := by
    apply (fl.trans (fd.trans fc)).mono
    intro i hi
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    tauto
  have hq' : addressValue quotient = a/b := by simpa using hqvalue
  have hr' : addressValue remainder = a%b := by simpa using hrvalue
  refine ⟨20*a.bits.length+15*b.bits.length+38+((dc+1)+cc), t, ?_,
    el.seq (ecall.seq ec), hq' ▸ hq, hr' ▸ hr, frame.word (by decide) ha,
    frame.word (by decide) hb, htready, frame⟩
  have hn : a.bits.length+1 ≤ a.bits.length+b.bits.length+2 := by omega
  have hdBound : dc ≤ 400*(a.bits.length+b.bits.length+2)^2 :=
    hdc.trans (by nlinarith)
  nlinarith [sq_nonneg (a.bits.length+b.bits.length+2 : ℤ)]

end Maxwell.Cost.RationalCanonical
