import Maxwell.Cost.NormalizeSource.RhsEntry
import Maxwell.Cost.LogRats
import Maxwell.Cost.Structured.Counted

namespace Maxwell.Cost.NormalizeSource.Rhs
open Structured RationalAccumulator

def Width (scaleNum scaleDen precision B : ℕ) (q : ℚ) : Prop :=
  (∀ i, 30 ≤ i → i ≤ 34 →
    (NormalizeCoefficient.values (Codec.RationalPair.canonical q) scaleNum scaleDen precision i).bits.length ≤ B) ∧
  (numerator scaleNum scaleDen precision q).natAbs.bits.length ≤ B

def records (scaleNum scaleDen precision : ℕ) (entries : List ℚ) : List Bool :=
  entries.flatMap (record scaleNum scaleDen precision)

def loopCode : Code := Counted.code 76 entryCode

def loopPrice (counterBits : List Bool) (entries : List ℚ) (B : ℕ) : ℕ :=
  (entries.length+1)*(13*counterBits.length+15)+entries.length*(120000*(B+2)^2)

structure LoopFrame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ≠ 76 → i ∉ work → t.tapes i = s.tapes i

theorem LoopFrame.trans {s t u : BitRAMState} (h : LoopFrame s t) (k : LoopFrame t u) :
    LoopFrame s u :=
  ⟨k.memory.trans h.memory, k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i h76 hi => (k.tapes i h76 hi).trans (h.tapes i h76 hi)⟩

private theorem counter_ready {s t : Store} (h : Counted.Frame 76 s t) (hr : Ready s.val) :
    Ready t.val := by
  have ht := h.2.2.2.2.2.1
  refine ⟨?_, ?_, blank_of_eq (ht 4 (by decide)) hr.four, ?_⟩
  · intro i hi hj
    exact word_of_eq (ht i (by omega)) (hr.bank i hi hj)
  · exact ⟨blank_of_eq (ht 0 (by decide)) hr.scratch.1,
      word_of_eq (ht 1 (by decide)) hr.scratch.2.1,
      blank_of_eq (ht 2 (by decide)) hr.scratch.2.2.1,
      blank_of_eq (ht 3 (by decide)) hr.scratch.2.2.2⟩
  · exact ⟨(ht 10 (by decide)).trans hr.parser.1,
      (ht 12 (by decide)).trans hr.parser.2.1,
      (ht 13 (by decide)).trans hr.parser.2.2⟩

private theorem counter_frame {s t : Store} (h : Counted.Frame 76 s t) : LoopFrame s.val t.val :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun i h76 _ => h.2.2.2.2.2.1 i h76⟩

private theorem body_frame {s t : BitRAMState} (h : Frame s t) : LoopFrame s t :=
  ⟨h.memory, h.randomCursor, h.output, fun i _ hi => h.tapes i hi⟩

/-- A fixed finite binary-counted loop normalizes every original RHS
coefficient and retains each signed dyadic numerator. -/
theorem loop_executes (entries : List ℚ) (scaleNum scaleDen precision B : ℕ)
    (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hwidth : ∀ p ∈ entries, Width scaleNum scaleDen precision B p)
    (counterBits preceding suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length)
    (hvalue : addressValue counterBits = entries.length)
    (hcounter : s.val.tapes 76 = BitTape.ofList counterBits)
    (hready : Ready s.val) (hscaleN : Word s.val 86 scaleNum)
    (hscaleD : Word s.val 87 scaleDen) (hpower : Word s.val 82 (2^precision))
    (harchive : s.val.tapes 88 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ loopPrice counterBits entries B ∧
      Executes (preceding ++ (LogRats.records entries ++ suffix)) tape loopCode cost s t ∧
      t.val.inputHead = s.val.inputHead+(LogRats.records entries).length ∧
      t.val.tapes 88 = BitTape.atEnd (archive ++ records scaleNum scaleDen precision entries) ∧
      Ready t.val ∧ LoopFrame s.val t.val := by
  induction entries generalizing counterBits preceding archive s with
  | nil =>
    obtain ⟨t, et, _, hz, hf⟩ := Counted.test_executes 76
      (preceding ++ (LogRats.records [] ++ suffix)) tape s counterBits hcounter
    refine ⟨13*counterBits.length+15, t, by simp [loopPrice],
      et.seq (Executes.done (hz.mpr hvalue)), ?_, ?_, counter_ready hf hready, counter_frame hf⟩
    · simpa [LogRats.records] using hf.2.1
    · simpa [records] using (hf.2.2.2.2.2.1 88 (by decide)).trans harchive
  | cons p entries ih =>
    let input := preceding ++ (LogRats.records (p::entries) ++ suffix)
    obtain ⟨tested, et, htword, hz, htf⟩ := Counted.test_executes 76 input tape s counterBits hcounter
    have hpred : addressValue (subtractBit true counterBits) = entries.length := by
      rw [subtractBit_pred counterBits (by simp [hvalue]), hvalue]
      simp
    have htrue : tested.val.registers 29 = true := by
      cases h : tested.val.registers 29 with
      | true => rfl
      | false => have := hz.mp h; simp only [List.length_cons] at hvalue; omega
    have hwt := htf.2.2.2.2.2.1
    have hp := hwidth p (by simp)
    obtain ⟨c, middle, hc, em, hmhead, hmlog, hmready, hmf⟩ := entry_executes
      p scaleNum scaleDen precision B hscaleNum hscaleDen hp.1 hp.2 preceding (LogRats.records entries ++ suffix) archive tape
      tested (htf.2.1.trans hhead) (counter_ready htf hready)
      (word_of_eq (hwt 86 (by decide)) hscaleN) (word_of_eq (hwt 87 (by decide)) hscaleD)
      (word_of_eq (hwt 82 (by decide)) hpower) ((hwt 88 (by decide)).trans harchive)
    have hi : preceding ++ (Codec.rat p ++
        (LogRats.records entries ++ suffix)) = input := by
      simp [input, LogRats.records, Codec.rat, List.append_assoc]
    rw [hi] at em
    have hmword : middle.val.tapes 76 = BitTape.ofList (subtractBit true counterBits) :=
      (hmf.tapes 76 (by decide)).trans htword
    have hmiddlehead : middle.val.inputHead = (preceding ++ Codec.rat p).length := by
      simpa [htf.2.1, hhead, Codec.rat] using hmhead
    obtain ⟨c', t, hc', erest, hthead, htlog, htready, hff⟩ := ih
      (fun p hp => hwidth p (by simp [hp])) (subtractBit true counterBits)
      (preceding ++ Codec.rat p)
      (archive ++ record scaleNum scaleDen precision p) middle hmiddlehead hpred hmword hmready
      (word_of_eq ((hmf.tapes 86 (by decide)).trans (hwt 86 (by decide))) hscaleN)
      (word_of_eq ((hmf.tapes 87 (by decide)).trans (hwt 87 (by decide))) hscaleD)
      (word_of_eq ((hmf.tapes 82 (by decide)).trans (hwt 82 (by decide))) hpower) hmlog
    have hi' : (preceding ++ Codec.rat p) ++ (LogRats.records entries ++ suffix) = input := by
      simp [input, LogRats.records, Codec.rat, List.append_assoc]
    rw [hi'] at erest
    change Executes input tape (.seq (Counted.test 76) (.loop 29 (.seq entryCode (Counted.test 76))))
      c' middle t at erest
    cases erest with
    | seq restTest restLoop =>
      refine ⟨_, t, ?_, et.seq (Executes.more htrue (em.seq restTest) restLoop), ?_, ?_, htready,
        ((counter_frame htf).trans (body_frame hmf)).trans hff⟩
      · dsimp [loopPrice] at hc' ⊢
        simp only [subtractBit_length] at hc' ⊢
        nlinarith
      · simp only [LogRats.records, List.flatMap_cons, List.length_append] at *
        dsimp only [Codec.rat] at *
        omega
      · simpa [records, List.append_assoc] using htlog

end Maxwell.Cost.NormalizeSource.Rhs
