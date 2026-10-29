import Maxwell.Cost.MagnitudeMax.Loop
import Maxwell.Cost.DecoderParser.ReadFields

namespace Maxwell.Cost.MagnitudeMax.Parse

open Structured RationalAccumulator

/-- The list length is parsed by fixed instructions and stored on tape 14. -/
def code : Code := .seq (DecoderParser.readNatural 14) Loop.code

def price (qs : List ℚ) (B : ℕ) : ℕ :=
  21 * qs.length.bits.length + 16 + Loop.price qs.length.bits qs B

theorem executes (qs : List ℚ) (current : Pair) (B : ℕ)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length)
    (hcounter : s.val.tapes 14 = BitTape.blank)
    (hpositive : 0 < current.2)
    (hcurrent : current.1.bits.length ≤ B ∧ current.2.bits.length ≤ B)
    (hwidth : ∀ q ∈ qs, q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (hbank : Bank s.val (bankOf current)) (hready : Scratch s.val 0)
    (hparser : LogRat.Ready s.val) (harchive : s.val.tapes 20 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ price qs B ∧
      Executes (preceding ++ (Codec.list Codec.rat qs ++ suffix)) tape code cost s t ∧
      t.val.inputHead = s.val.inputHead + (Codec.list Codec.rat qs).length ∧
      Bank t.val (bankOf (scan current qs)) ∧ Scratch t.val 0 ∧ LogRat.Ready t.val ∧
      t.val.tapes 20 = BitTape.atEnd (archive ++ Loop.records qs) ∧ Loop.Frame s.val t.val := by
  let input := preceding ++ (Codec.list Codec.rat qs ++ suffix)
  obtain ⟨u, hu, huhead, huword, hu10, huf⟩ := DecoderParser.readNatural_steps 14 (by decide)
    qs.length preceding (Loop.records qs ++ suffix) tape s hhead hparser.1 hcounter
  have hi : preceding ++ (Codec.nat qs.length ++ (Loop.records qs ++ suffix)) = input := by
    simp [input, Codec.list, Loop.records, List.append_assoc]
  rw [hi] at hu
  have huother (i : ℕ) (hi : i ≠ 14) : u.val.tapes i = s.val.tapes i :=
    huf.tapes i (by simpa using hi)
  have hubank : Bank u.val (bankOf current) := by
    intro i hi hi'
    exact word_of_eq (huother i (by omega)) (hbank i hi hi')
  have huready : Scratch u.val 0 :=
    ⟨blank_of_eq (huother 0 (by decide)) hready.1,
      word_of_eq (huother 1 (by decide)) hready.2.1,
      blank_of_eq (huother 2 (by decide)) hready.2.2.1,
      blank_of_eq (huother 3 (by decide)) hready.2.2.2⟩
  have huparser : LogRat.Ready u.val :=
    ⟨hu10, (huother 12 (by decide)).trans hparser.2.1,
      (huother 13 (by decide)).trans hparser.2.2⟩
  have hunext : u.val.inputHead = (preceding ++ Codec.nat qs.length).length := by
    simpa [hhead] using huhead
  obtain ⟨c, t, hc, ht, hthead, htbank, htready, htparser, htlog, htf⟩ :=
    Loop.executes qs current B qs.length.bits (preceding ++ Codec.nat qs.length)
      suffix archive tape u hunext (addressValue_bits qs.length) huword hpositive hcurrent
      hwidth hubank huready huparser ((huother 20 (by decide)).trans harchive)
  have hi' : (preceding ++ Codec.nat qs.length) ++ (Loop.records qs ++ suffix) = input := by
    simp [input, Codec.list, Loop.records, List.append_assoc]
  rw [hi'] at ht
  refine ⟨21 * qs.length.bits.length + 16 + c, t, by dsimp [price]; omega,
    hu.seq ht, ?_, htbank, htready, htparser, htlog, ?_⟩
  · simp only [Codec.list, List.length_append]
    dsimp only [Loop.records] at hthead
    omega
  · refine ⟨htf.1.trans huf.address, htf.2.1.trans huf.memory,
      htf.2.2.1.trans huf.randomCursor, htf.2.2.2.1.trans huf.output, ?_⟩
    intro i h4 h10 h12 h13 h14 h20 hb
    exact (htf.2.2.2.2 i h4 h10 h12 h13 h14 h20 hb).trans (huother i h14)

end Maxwell.Cost.MagnitudeMax.Parse
