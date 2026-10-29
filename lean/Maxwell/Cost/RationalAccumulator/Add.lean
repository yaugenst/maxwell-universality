import Maxwell.Cost.RationalAccumulator.Bank
import Maxwell.Cost.StoredAdd
import Maxwell.Cost.PadWord

namespace Maxwell.Cost.RationalAccumulator

open Structured

/-- The padding steps make zero an ordinary arithmetic operand. The last
normalization restores the caller's canonical scalar word. -/
def addCode (target : ℕ) : Code :=
  .seq (.call (PadWord.program 1))
    (.seq (.call (PadWord.program target))
      (.seq (.call (StoredAdd.program target)) (.call (NormalizeWord.program 1))))

private theorem pad_frame {workTape : ℕ} {s t : BitRAMState}
    (hw : workTape < 4 ∨ (30 ≤ workTape ∧ workTape ≤ 36))
    (h : TapeOps.Frame workTape workTape s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 hb => ht i (by omega) (by omega),
    fun i _ _ _ h26 h27 => hg i h26 h27⟩

private theorem add_frame {target : ℕ} {s t : BitRAMState}
    (ht : 30 ≤ target) (ht' : target ≤ 36)
    (h : StoredAdd.Frame target s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, htapes, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 hb => htapes i (by omega) (by omega),
    fun i h15 h24 h25 h26 h27 => hg i (by omega) h24 h25 h26 h27⟩

private theorem normalize_one_frame {s t : BitRAMState}
    (h : NormalizeWord.Frame 1 s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 _ => ht i (by omega),
    fun i _ h24 h25 h26 h27 => hg i h24 h25 h26 h27⟩

/-- One actual finite program adds the canonical scalar word to a bank
entry. All seven bank entries and the reusable scratch contract are tracked. -/
theorem add_bank (target : ℕ) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (scalar : ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val scalar) :
    ∃ cost, ∃ t : Store, cost ≤ 200 * (scalar.bits.length + (v target).bits.length + 4) ∧
      Executes input tape (addCode target) cost s t ∧
      Bank t.val (Function.update v target (scalar + v target)) ∧
      Scratch t.val scalar ∧ Frame s.val t.val := by
  obtain ⟨ao, h0⟩ := hready.1
  obtain ⟨xo, h1⟩ := hready.2.1
  obtain ⟨zo, h2⟩ := hready.2.2.1
  obtain ⟨yo, h3⟩ := hready.2.2.2
  obtain ⟨origin, hw⟩ := hbank target ht ht'
  obtain ⟨padScalarCost, hpCost, hp, hpWord, hpFrame⟩ :=
    PadWord.simulation 1 xo input tape scalar.bits s.val s.property h1
  let p : Store := Store.ofState (PadWord.finish 1 s.val scalar.bits)
  have hep : Executes input tape (.call (PadWord.program 1)) (padScalarCost + 1) s p :=
    Executes.call _ _ _ _ hp (by simp [PadWord.program, PadWord.finish])
  have hpTarget : p.val.tapes target = BitTape.shifted (v target).bits origin :=
    (hpFrame.2.2.2.2.2.1 target (by omega) (by omega)).trans hw
  obtain ⟨padTargetCost, hqCost, hq, hqWord, hqFrame⟩ :=
    PadWord.simulation target origin input tape (v target).bits p.val p.property hpTarget
  let q : Store := Store.ofState (PadWord.finish target p.val (v target).bits)
  have heq : Executes input tape (.call (PadWord.program target)) (padTargetCost + 1) p q :=
    Executes.call _ _ _ _ hq (by simp [PadWord.program, PadWord.finish])
  have hq0 : q.val.tapes 0 = {BitTape.blank with head := ao} :=
    (hqFrame.2.2.2.2.2.1 0 (by omega) (by omega)).trans
      ((hpFrame.2.2.2.2.2.1 0 (by omega) (by omega)).trans h0)
  have hq1 : q.val.tapes 1 = BitTape.shifted (PadWord.bits scalar.bits) xo :=
    (hqFrame.2.2.2.2.2.1 1 (by omega) (by omega)).trans hpWord
  have hq2 : q.val.tapes 2 = {BitTape.blank with head := zo} :=
    (hqFrame.2.2.2.2.2.1 2 (by omega) (by omega)).trans
      ((hpFrame.2.2.2.2.2.1 2 (by omega) (by omega)).trans h2)
  obtain ⟨addCost, added, haCost, ha, hap, haWord, ha0, ha1, ha2, haFrame⟩ :=
    StoredAdd.simulation target (by omega) input tape (PadWord.bits scalar.bits)
      (PadWord.bits (v target).bits) ao xo zo origin (PadWord.nonempty _) (PadWord.nonempty _)
      q.val q.property hq0 hq1 hq2 hqWord
  let a : Store := Store.ofState added
  have hea : Executes input tape (.call (StoredAdd.program target)) (addCost + 1) q a :=
    Executes.call _ _ _ _ ha (by
      simp [StoredAdd.program, hap, WordTransfer.move, TapeOps.copyClear,
        Rewind.program, NormalizeWord.program, ScanForward.program, TapeOps.trim,
        TapeOps.clear, RewindOvershoot.program, RewindOvershoot.preamble,
        BitRAM.link, rippleAdder, BitRAMInstruction.relocate])
  obtain ⟨normCost, normalized, hnCost, hn, hnp, hnWord, _, hnFrame⟩ :=
    NormalizeWord.simulation 1 xo input tape (PadWord.bits scalar.bits) a.val a.property ha1
  let t : Store := Store.ofState normalized
  have hen : Executes input tape (.call (NormalizeWord.program 1)) (normCost + 1) a t :=
    Executes.call _ _ _ _ hn (by
      simp [NormalizeWord.program, hnp, ScanForward.program, TapeOps.trim,
        Rewind.program, BitRAMInstruction.relocate])
  have hpa : Frame s.val p.val := pad_frame (Or.inl (by omega)) hpFrame
  have hqa : Frame p.val q.val := pad_frame (Or.inr ⟨ht, ht'⟩) hqFrame
  have haa : Frame q.val a.val := add_frame ht ht' haFrame
  have hna : Frame a.val t.val := normalize_one_frame hnFrame
  refine ⟨(padScalarCost + 1) + ((padTargetCost + 1) + ((addCost + 1) + (normCost + 1))),
    t, ?_, hep.seq (heq.seq (hea.seq hen)), ?_, ?_, ((hpa.trans hqa).trans haa).trans hna⟩
  · have hpl := PadWord.length_le scalar.bits
    have hql := PadWord.length_le (v target).bits
    omega
  · intro i hi hi'
    by_cases hit : i = target
    · subst i
      refine ⟨origin + (PadWord.bits (v target).bits).length, ?_⟩
      have hout := (hnFrame.2.2.2.2.2.1 target (by omega)).trans haWord
      simpa [t, Store.ofState] using hout
    · simp only [Function.update_of_ne hit]
      exact word_of_eq ((hnFrame.2.2.2.2.2.1 i (by omega)).trans
        ((haFrame.2.2.2.2.2.1 i (by omega) hit).trans
          ((hqFrame.2.2.2.2.2.1 i hit hit).trans
            (hpFrame.2.2.2.2.2.1 i (by omega) (by omega))))) (hbank i hi hi')
  · refine ⟨⟨ao + (PadWord.bits (v target).bits).length,
        (hnFrame.2.2.2.2.2.1 0 (by omega)).trans ha0⟩,
      ⟨xo, by simpa [t, Store.ofState] using hnWord⟩,
      ⟨zo + (scalar + v target).bits.length, ?_⟩, ⟨yo, ?_⟩⟩
    · have hout := (hnFrame.2.2.2.2.2.1 2 (by omega)).trans ha2
      simpa [t, Store.ofState] using hout
    · exact (hnFrame.2.2.2.2.2.1 3 (by omega)).trans
        ((haFrame.2.2.2.2.2.1 3 (by omega) (by omega)).trans
          ((hqFrame.2.2.2.2.2.1 3 (by omega) (by omega)).trans
            ((hpFrame.2.2.2.2.2.1 3 (by omega) (by omega)).trans h3)))

theorem add_compiled_run (target : ℕ) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (scalar : ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val scalar) :
    ∃ t : Store,
      (runPriced ((addCode target).compile.next input tape)
        (200 * (scalar.bits.length + (v target).bits.length + 4) + 1) s.val).finished =
        some (t.place (addCode target).size) ∧
      (runPriced ((addCode target).compile.next input tape)
        (200 * (scalar.bits.length + (v target).bits.length + 4) + 1) s.val).instructions ≤
        200 * (scalar.bits.length + (v target).bits.length + 4) ∧
      Bank t.val (Function.update v target (scalar + v target)) ∧
      Scratch t.val scalar ∧ Frame s.val t.val := by
  obtain ⟨cost, t, hc, he, hb, hs, hf⟩ := add_bank target ht ht' input tape v scalar s hbank hready
  have hr := he.compiled_run (200 * (scalar.bits.length + (v target).bits.length + 4) + 1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, hb, hs, hf⟩

end Maxwell.Cost.RationalAccumulator
