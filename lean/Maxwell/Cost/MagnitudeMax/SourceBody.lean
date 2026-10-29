import Maxwell.Cost.MagnitudeMax.Body
import Maxwell.Cost.MagnitudeMax.SourceLogger
import Maxwell.Cost.SourceGrouping.Boundary

namespace Maxwell.Cost.MagnitudeMax.SourceBody

open Structured RationalAccumulator

/-- One fixed sparse-record body updates the maximum, emits the next row
boundary, and retains all signed record fields. -/
def code : Code := .seq (.call ParseEntry.program)
  (.seq parsedCode (.seq (.call SourceGrouping.Boundary.program) (.call SourceLogger.program)))

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 15 → i ≠ 16 → i ≠ 18 → i ≠ 22 → i ≠ 24 →
    (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i)

theorem executes (row column : ℕ) (q : ℚ) (current : Pair) (B : ℕ) (previous : List Bool)
    (preceding suffix archive boundaries : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length)
    (hpositive : 0 < current.2)
    (hcurrent : current.1.bits.length ≤ B ∧ current.2.bits.length ≤ B)
    (hrow : row.bits.length ≤ B) (hcolumn : column.bits.length ≤ B)
    (hq : q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (hprev : previous.length ≤ B)
    (hbank : Bank s.val (bankOf current)) (hready : Scratch s.val 0)
    (hparser : LogEntry.Ready s.val) (harchive : s.val.tapes 18 = BitTape.atEnd archive)
    (hprevious : s.val.tapes 22 = BitTape.atEnd previous)
    (hboundaries : s.val.tapes 24 = BitTape.atEnd boundaries) :
    ∃ cost, ∃ t : Store, cost ≤ 12000 * (B + 2)^2 ∧
      Executes (preceding ++ (ParseEntry.encode row column q ++ suffix)) tape code cost s t ∧
      t.val.inputHead = s.val.inputHead + (ParseEntry.encode row column q).length ∧
      Bank t.val (bankOf (select current q)) ∧ Scratch t.val 0 ∧ LogEntry.Ready t.val ∧
      t.val.tapes 18 = BitTape.atEnd (archive ++ ParseEntry.encode row column q) ∧
      t.val.tapes 22 = BitTape.atEnd row.bits ∧
      t.val.tapes 24 = BitTape.atEnd (boundaries ++ [!((row.bits == previous) && s.val.registers 33)]) ∧
      t.val.registers 33 = true ∧ Frame s.val t.val := by
  let input := preceding ++ (ParseEntry.encode row column q ++ suffix)
  obtain ⟨p, hp, hppc, hphead, hpcount, hprow, hpcol, hpnum, hpden, hpsign, hpf⟩ :=
    ParseEntry.steps row column q preceding suffix tape s.val s.property hhead
      hparser.1 hparser.2.1 hparser.2.2.1 hparser.2.2.2.1 hparser.2.2.2.2
  let pS := Store.ofState p
  have hp' : Executes input tape (.call ParseEntry.program)
      (17 * LogEntry.width row column q + 40) s pS :=
    Executes.call _ _ _ _ hp (by simpa [hppc] using
      (show ParseEntry.program.code[83]? = some .halt by decide))
  have hpother (i : ℕ) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h15 : i ≠ 15) (h16 : i ≠ 16) : pS.val.tapes i = s.val.tapes i :=
    hpf.2.2.2.2.1 i h10 h12 h13 h15 h16
  have hpb : Bank pS.val (bankOf current) := by
    intro i hi hi'
    exact word_of_eq (hpother i (by omega) (by omega) (by omega) (by omega) (by omega)) (hbank i hi hi')
  have hpr : Scratch pS.val 0 :=
    ⟨blank_of_eq (hpother 0 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.1,
      word_of_eq (hpother 1 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.2.1,
      blank_of_eq (hpother 2 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.2.2.1,
      blank_of_eq (hpother 3 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.2.2.2⟩
  obtain ⟨c, u, hc, hu, hub, hur, husign, huf⟩ := parsed input tape (bankOf current) q B
    (by intro i hi; rcases hi with rfl | rfl <;> simp [bankOf, hcurrent]) hq.1 hq.2
    (by simpa [bankOf] using hpositive) (by simp [bankOf]) (by simp [bankOf])
    (by simp [bankOf]) (by simp [bankOf]) pS hpb hpr hpnum hpden
  have huother (i : ℕ) (hi : 4 ≤ i) (hj : i < 30 ∨ 36 < i) : u.val.tapes i = pS.val.tapes i :=
    huf.2.2.2.2.2.1 i hi hj
  obtain ⟨bc, b, hbc, hb, hbpc, hbrow, hbprevious, hbarchive, hbseen, hbf⟩ :=
    SourceGrouping.Boundary.simulation input tape row.bits previous boundaries u.val u.property
      ((huother 15 (by decide) (Or.inl (by decide))).trans hprow)
      ((huother 22 (by decide) (Or.inl (by decide))).trans
        ((hpother 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hprevious))
      ((huother 24 (by decide) (Or.inl (by decide))).trans
        ((hpother 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hboundaries))
  let bS := Store.ofState b
  have hb' : Executes input tape (.call SourceGrouping.Boundary.program) (bc + 1) u bS :=
    Executes.call _ _ _ _ hb (by simpa [hbpc] using SourceGrouping.Boundary.halt_instruction)
  have hbother (i : ℕ) (h15 : i ≠ 15) (h22 : i ≠ 22) (h24 : i ≠ 24) :
      bS.val.tapes i = u.val.tapes i := hbf.2.2.2.2.2.2 i h15 h22 h24
  have hretained (i : ℕ) (hi : 4 ≤ i) (hb : i < 30 ∨ 36 < i)
      (h15 : i ≠ 15) (h22 : i ≠ 22) (h24 : i ≠ 24) : bS.val.tapes i = pS.val.tapes i :=
    (hbother i h15 h22 h24).trans (huother i hi hb)
  obtain ⟨t, ht, hthead, htlog, htparser, htf⟩ := SourceLogger.steps input tape row column q archive bS
    ((hretained 10 (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hpcount)
    hbrow
    ((hretained 16 (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hpcol)
    ((hretained 12 (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hpnum)
    ((hretained 13 (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans hpden)
    (hbf.2.2.2.2.2.1.trans (husign.trans hpsign))
    ((hretained 18 (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans
      ((hpother 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans harchive))
  have htother (i : ℕ) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h15 : i ≠ 15) (h16 : i ≠ 16) (h18 : i ≠ 18) : t.val.tapes i = bS.val.tapes i :=
    htf.2.2.2.2.1 i h10 h12 h13 h15 h16 h18
  have hseen : u.val.registers 33 = s.val.registers 33 :=
    (huf.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      (hpf.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide))
  refine ⟨(17 * LogEntry.width row column q + 40) + (c + ((bc + 1) +
      (28 * LogEntry.width row column q + 130))), t, ?_, hp'.seq (hu.seq (hb'.seq ht)),
    hthead.trans (hbf.2.1.trans (huf.2.1.trans hphead)), ?_, ?_, htparser, htlog,
    (htother 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbprevious,
    ?_, (htf.2.2.2.2.2 33 (Or.inr (by decide))).trans hbseen, ?_⟩
  · dsimp [LogEntry.width] at *
    nlinarith [hq.1, hq.2]
  · rw [after_bankOf] at hub
    intro i hi hi'
    exact word_of_eq ((htother i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hbother i (by omega) (by omega) (by omega))) (hub i hi hi')
  · have htape (i : ℕ) (hi : i < 4) : t.val.tapes i = u.val.tapes i :=
      (htother i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (hbother i (by omega) (by omega) (by omega))
    exact ⟨blank_of_eq (htape 0 (by decide)) hur.1, word_of_eq (htape 1 (by decide)) hur.2.1,
      blank_of_eq (htape 2 (by decide)) hur.2.2.1, blank_of_eq (htape 3 (by decide)) hur.2.2.2⟩
  · simpa [hseen] using
      (htother 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbarchive
  · refine ⟨htf.1.trans (hbf.1.trans (huf.1.trans hpf.1)),
      htf.2.1.trans (hbf.2.2.1.trans (huf.2.2.1.trans hpf.2.1)),
      htf.2.2.1.trans (hbf.2.2.2.1.trans (huf.2.2.2.1.trans hpf.2.2.1)),
      htf.2.2.2.1.trans (hbf.2.2.2.2.1.trans (huf.2.2.2.2.1.trans hpf.2.2.2.1)), ?_⟩
    intro i h4 h10 h12 h13 h15 h16 h18 h22 h24 hib
    exact (htother i h10 h12 h13 h15 h16 h18).trans
      ((hretained i h4 hib h15 h22 h24).trans (hpother i h10 h12 h13 h15 h16))

end Maxwell.Cost.MagnitudeMax.SourceBody
