import Maxwell.Cost.NormalizeSource.RhsLoop
import Maxwell.Cost.DecoderParser.ReadFields

namespace Maxwell.Cost.NormalizeSource.Rhs
open Structured RationalAccumulator

/-- The real list header supplies the binary countdown on fresh tape 76. -/
def code : Code := .seq (DecoderParser.readNatural 76) loopCode

def price (qs : List ℚ) (B : ℕ) : ℕ :=
  21*qs.length.bits.length+16+loopPrice qs.length.bits qs B

/-- Normalize and serialize the complete RHS list from its canonical wire.
All matrix metadata and its completed coefficient archive survive. -/
theorem executes (qs : List ℚ) (scaleNum scaleDen precision B : ℕ)
    (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hwidth : ∀ q ∈ qs, Width scaleNum scaleDen precision B q)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length) (hcounter : s.val.tapes 76 = BitTape.blank)
    (hready : Ready s.val) (hscaleN : Word s.val 86 scaleNum) (hscaleD : Word s.val 87 scaleDen)
    (hpower : Word s.val 82 (2^precision)) (harchive : s.val.tapes 88 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ price qs B ∧
      Executes (preceding ++ (Codec.list Codec.rat qs ++ suffix)) tape code cost s t ∧
      t.val.inputHead = s.val.inputHead+(Codec.list Codec.rat qs).length ∧
      t.val.tapes 88 = BitTape.atEnd (archive ++ records scaleNum scaleDen precision qs) ∧
      Ready t.val ∧ LoopFrame s.val t.val := by
  let input := preceding ++ (Codec.list Codec.rat qs ++ suffix)
  obtain ⟨u, hu, huhead, huword, hu10, huf⟩ := DecoderParser.readNatural_steps 76 (by decide)
    qs.length preceding (LogRats.records qs ++ suffix) tape s hhead hready.parser.1 hcounter
  have hi : preceding ++ (Codec.nat qs.length ++ (LogRats.records qs ++ suffix)) = input := by
    simp [input, Codec.list, LogRats.records, List.append_assoc]
  rw [hi] at hu
  have uk (i : ℕ) (hi : i ≠ 76) : u.val.tapes i = s.val.tapes i := huf.tapes i (by simpa using hi)
  have ur : Ready u.val := by
    refine ⟨?_, ?_, blank_of_eq (uk 4 (by decide)) hready.four, ?_⟩
    · intro i hi hj
      exact word_of_eq (uk i (by omega)) (hready.bank i hi hj)
    · exact ⟨blank_of_eq (uk 0 (by decide)) hready.scratch.1,
        word_of_eq (uk 1 (by decide)) hready.scratch.2.1,
        blank_of_eq (uk 2 (by decide)) hready.scratch.2.2.1,
        blank_of_eq (uk 3 (by decide)) hready.scratch.2.2.2⟩
    · exact ⟨hu10, (uk 12 (by decide)).trans hready.parser.2.1,
        (uk 13 (by decide)).trans hready.parser.2.2⟩
  have hunext : u.val.inputHead = (preceding ++ Codec.nat qs.length).length := by simpa [hhead] using huhead
  obtain ⟨c, t, hc, ht, hthead, htlog, htready, htf⟩ := loop_executes qs scaleNum scaleDen precision B
    hscaleNum hscaleDen hwidth qs.length.bits (preceding ++ Codec.nat qs.length) suffix archive tape
    u hunext (addressValue_bits qs.length) huword ur
    (word_of_eq (uk 86 (by decide)) hscaleN) (word_of_eq (uk 87 (by decide)) hscaleD)
    (word_of_eq (uk 82 (by decide)) hpower) ((uk 88 (by decide)).trans harchive)
  have hi' : (preceding ++ Codec.nat qs.length) ++ (LogRats.records qs ++ suffix) = input := by
    simp [input, Codec.list, LogRats.records, List.append_assoc]
  rw [hi'] at ht
  refine ⟨21*qs.length.bits.length+16+c, t, by dsimp [price]; omega, hu.seq ht, ?_, htlog, htready, ?_⟩
  · simp only [Codec.list, List.length_append]
    dsimp only [LogRats.records] at hthead
    omega
  · refine ⟨htf.memory.trans huf.memory, htf.randomCursor.trans huf.randomCursor,
      htf.output.trans huf.output, ?_⟩
    intro i h76 hi
    exact (htf.tapes i h76 hi).trans (uk i h76)

theorem price_le (qs : List ℚ) (B : ℕ) :
    price qs B ≤ 120100*(qs.length+1)*((B+2)^2+qs.length.bits.length+1) := by
  dsimp [price, loopPrice]
  nlinarith

end Maxwell.Cost.NormalizeSource.Rhs
