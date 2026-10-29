import Maxwell.Cost.MagnitudeMax.Reset
import Maxwell.Cost.MagnitudeMax.Rhs
import Maxwell.Cost.MagnitudeMax.Zero
import Maxwell.Cost.MagnitudeMax.SourceSemantics

namespace Maxwell.Cost.MagnitudeMax.Tail

open Structured RationalAccumulator

def code : Code := .seq (Save.code 80 81)
  (.seq Reset.code (.seq (.call Rhs.program) (.seq (Save.code 86 87) Zero.code)))

def price (qs : List ℚ) (B : ℕ) : ℕ := Parse.price qs B + 72 * B + 86

def work : Finset ℕ := {0, 1, 2, 3, 10, 12, 13, 20, 21, 30, 31, 32, 33, 34, 35, 36, 80, 81, 86, 87}

theorem rhs_frame {s t : BitRAMState} (h : Rhs.Frame s t) : DecoderParser.Frame work s t := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro i hi
  simp only [work, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact h.2.2.2.2 i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Save the matrix pair, compute the RHS maximum during its one parse,
save the RHS pair, and perform an actual constant-cost zero-RHS test. -/
theorem executes (matrix : Pair) (qs : List ℚ) (B : ℕ) (hB : 1 ≤ B)
    (hmat : matrix.1.bits.length ≤ B ∧ matrix.2.bits.length ≤ B)
    (hwidth : ∀ q ∈ qs, q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (preceding suffix : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length)
    (hbank : Bank s.val (bankOf matrix)) (hready : Scratch s.val 0) (hparser : LogRat.Ready s.val)
    (h20 : s.val.tapes 20 = BitTape.atEnd []) (h21 : s.val.tapes 21 = BitTape.blank)
    (h80 : Blank s.val 80) (h81 : Blank s.val 81) (h86 : Blank s.val 86) (h87 : Blank s.val 87) :
    ∃ cost, ∃ t : Store, cost ≤ price qs B ∧
      Executes (preceding ++ (Codec.list Codec.rat qs ++ suffix)) tape code cost s t ∧
      t.val.inputHead = s.val.inputHead + (Codec.list Codec.rat qs).length ∧
      Word t.val 80 matrix.1 ∧ Word t.val 81 matrix.2 ∧
      Word t.val 86 (maximum qs).1 ∧ Word t.val 87 (maximum qs).2 ∧
      t.val.registers 90 = decide ((maximum qs).1 = 0) ∧
      t.val.tapes 20 = BitTape.atEnd (Loop.records qs) ∧ Scratch t.val 0 ∧ LogRat.Ready t.val ∧
      DecoderParser.Frame work s.val t.val ∧ Bank t.val (bankOf (maximum qs)) := by
  let input := preceding ++ (Codec.list Codec.rat qs ++ suffix)
  obtain ⟨u, hu, hu80, hu81, huhead, huf⟩ := Save.pair 80 81 (by decide) (by decide) (by decide)
    matrix input tape s (by simpa [bankOf] using hbank 30 (by decide) (by decide))
    (by simpa [bankOf] using hbank 31 (by decide) (by decide)) h80 h81
  have hub : Bank u.val (bankOf matrix) := by
    intro i hi hi'
    exact word_of_eq (huf.tapes i (by simp; omega)) (hbank i hi hi')
  have hur : Scratch u.val 0 :=
    ⟨blank_of_eq (huf.tapes 0 (by simp)) hready.1, word_of_eq (huf.tapes 1 (by simp)) hready.2.1,
      blank_of_eq (huf.tapes 2 (by simp)) hready.2.2.1, blank_of_eq (huf.tapes 3 (by simp)) hready.2.2.2⟩
  obtain ⟨v, hv, hvb, hvr, hvhead, hvf⟩ := Reset.executes matrix input tape u hub hur
  have hvother (i : ℕ) (hi : i ∉ Reset.work) (hi' : i ∉ ({80, 81} : Finset ℕ)) :
      v.val.tapes i = s.val.tapes i := (hvf.tapes i hi).trans (huf.tapes i hi')
  have hvparser : LogRat.Ready v.val :=
    ⟨(hvother 10 (by decide) (by decide)).trans hparser.1,
      (hvother 12 (by decide) (by decide)).trans hparser.2.1,
      (hvother 13 (by decide) (by decide)).trans hparser.2.2⟩
  obtain ⟨c, r, hc, hr, hrhead, hrbank, hrr, hrparser, hrlog, hrf⟩ := Rhs.executes qs (0, 1) B preceding suffix [] tape v
    ((hvhead.trans huhead).trans hhead) ((hvother 21 (by decide) (by decide)).trans h21)
    (by decide) (by simp [hB]) hwidth hvb hvr hvparser
    ((hvother 20 (by decide) (by decide)).trans h20)
  have hrother (i : ℕ) (h4 : 4 ≤ i) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h21 : i ≠ 21) (h20 : i ≠ 20) (hb : i < 30 ∨ 36 < i) : r.val.tapes i = v.val.tapes i :=
    hrf.2.2.2.2 i h4 h10 h12 h13 h21 h20 hb
  have hrblank (i : ℕ) (hi : i = 86 ∨ i = 87) : Blank r.val i := by
    rcases hi with rfl | rfl
    · exact blank_of_eq ((hrother 86 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (Or.inr (by decide))).trans (hvother 86 (by decide) (by decide))) h86
    · exact blank_of_eq ((hrother 87 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (Or.inr (by decide))).trans (hvother 87 (by decide) (by decide))) h87
  obtain ⟨w, hw, hw86, hw87, hwhead, hwf⟩ := Save.pair 86 87 (by decide) (by decide) (by decide)
    (maximum qs) input tape r (by simpa [bankOf, maximum] using hrbank 30 (by decide) (by decide))
    (by simpa [bankOf, maximum] using hrbank 31 (by decide) (by decide))
    (hrblank 86 (Or.inl rfl)) (hrblank 87 (Or.inr rfl))
  obtain ⟨hz, hztest, _, hzf⟩ := Zero.executes (maximum qs).1 input tape w hw86
  have hfinal (i : ℕ) (hi : i = 80 ∨ i = 81) : (Zero.finish w).val.tapes i = u.val.tapes i := by
    rcases hi with rfl | rfl
    · exact (hzf.tapes 80 (by simp)).trans ((hwf.tapes 80 (by simp)).trans
        ((hrother 80 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (Or.inr (by decide))).trans (hvf.tapes 80 (by decide))))
    · exact (hzf.tapes 81 (by simp)).trans ((hwf.tapes 81 (by simp)).trans
        ((hrother 81 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (Or.inr (by decide))).trans (hvf.tapes 81 (by decide))))
  have hwr : Scratch w.val 0 :=
    ⟨blank_of_eq (hwf.tapes 0 (by simp)) hrr.1, word_of_eq (hwf.tapes 1 (by simp)) hrr.2.1,
      blank_of_eq (hwf.tapes 2 (by simp)) hrr.2.2.1, blank_of_eq (hwf.tapes 3 (by simp)) hrr.2.2.2⟩
  have hzother (i : ℕ) (hi : i ∉ ({86, 87} : Finset ℕ)) : (Zero.finish w).val.tapes i = r.val.tapes i :=
    (hzf.tapes i (by simp)).trans (hwf.tapes i hi)
  refine ⟨_, Zero.finish w, ?_, hu.seq (hv.seq (hr.seq (hw.seq hz))), ?_,
    word_of_eq (hfinal 80 (Or.inl rfl)) hu80, word_of_eq (hfinal 81 (Or.inr rfl)) hu81,
    word_of_eq (hzf.tapes 86 (by simp)) hw86, word_of_eq (hzf.tapes 87 (by simp)) hw87,
    hztest, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hnum, hden⟩ := maximum_width qs B B hB (fun q hq => (hwidth q hq).1) (fun q hq => (hwidth q hq).2)
    dsimp [price]
    omega
  · change w.val.inputHead = s.val.inputHead + (Codec.list Codec.rat qs).length
    omega
  · simpa using (hzother 20 (by simp)).trans hrlog
  · exact ⟨blank_of_eq (hzf.tapes 0 (by simp)) hwr.1, word_of_eq (hzf.tapes 1 (by simp)) hwr.2.1,
      blank_of_eq (hzf.tapes 2 (by simp)) hwr.2.2.1, blank_of_eq (hzf.tapes 3 (by simp)) hwr.2.2.2⟩
  · exact ⟨(hzother 10 (by simp)).trans hrparser.1, (hzother 12 (by simp)).trans hrparser.2.1,
      (hzother 13 (by simp)).trans hrparser.2.2⟩
  · exact ((((huf.mono (by decide)).trans (hvf.mono (by decide))).trans
      (rhs_frame hrf)).trans (hwf.mono (by decide))).trans (hzf.mono (by simp))
  · intro i hi hi'
    have h := word_of_eq (hzother i (by simp; omega)) (hrbank i hi hi')
    simpa [maximum] using h

end Maxwell.Cost.MagnitudeMax.Tail
