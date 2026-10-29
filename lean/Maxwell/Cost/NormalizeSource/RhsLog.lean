import Maxwell.Cost.NormalizeSource.RhsNormalize
import Maxwell.Cost.SourceCircuit.NormalizedRecord

namespace Maxwell.Cost.NormalizeSource.Rhs
open Structured RationalAccumulator

def logCode : Code := .seq (SourceCircuit.appendBitCode 88 23)
  (.seq (.call (WordTransfer.move 4 12))
    (.seq (.call (ScanForward.program 12)) (.call (LogNat.program 12 88))))

def logWork : Finset ℕ := {4,12,88}

structure LogFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ logWork → t.tapes i = s.tapes i

/-- Serialize the signed canonical integer numerator and reclaim its
arithmetic result word. The dyadic denominator stays on tape 82. -/
theorem logs (input : List Bool) (tape : ℕ → Bool) (z : ℤ) (archive : List Bool) (s : Store)
    (hout : SignedRound.Output s.val z) (h12 : s.val.tapes 12 = BitTape.blank)
    (harchive : s.val.tapes 88 = BitTape.atEnd archive) :
    ∃ t : Store, Executes input tape logCode (45*z.natAbs.bits.length+50) s t ∧
      t.val.tapes 88 = BitTape.atEnd (archive ++ Codec.int z) ∧
      Blank t.val 4 ∧ t.val.tapes 12 = BitTape.blank ∧
      LogFrame s.val t.val := by
  obtain ⟨origin, hout, hsign⟩ := hout
  obtain ⟨a, ea, hat, _, haf⟩ := SourceCircuit.appendBit_executes 88 23 input tape archive s harchive
  have ha4 : a.val.tapes 4 = BitTape.shifted z.natAbs.bits origin := by simpa [hat] using hout
  have ha12 : a.val.tapes 12 = {BitTape.blank with head := (0 : ℤ)} := by simpa [hat, BitTape.blank] using h12
  obtain ⟨b, eb, hbp, hb4, hb12, hbf⟩ := WordTransfer.move_steps 4 12 (by decide) input tape
    z.natAbs.bits origin 0 a.val a.property ha4 ha12
  let bs := Store.ofState b
  have eb' : Executes input tape (.call (WordTransfer.move 4 12))
      (12*z.natAbs.bits.length+11) a bs := Executes.call _ _ _ _ eb (by rw [hbp]; rfl)
  obtain ⟨ec, hc12, hcf⟩ := ScanForward.shifted_steps 12 0 input tape z.natAbs.bits bs.val bs.property hb12
  let c := Store.ofState (ScanForward.finish 12 z.natAbs.bits.length bs.val)
  have ec' : Executes input tape (.call (ScanForward.program 12))
      (5*z.natAbs.bits.length+4) bs c := Executes.call _ _ _ _ ec rfl
  have hc12' : c.val.tapes 12 = BitTape.atEnd z.natAbs.bits := by
    simpa [c, Store.ofState, BitTape.shiftedEnd, BitTape.shifted, BitTape.atEnd, BitTape.ofList] using hc12
  have hc88 : c.val.tapes 88 = BitTape.atEnd (archive ++ [decide (z<0)]) := by
    exact (hcf.2.2.2.2.2.1 88 (by decide) (by decide)).trans
      ((hbf.2.2.2.2.2.1 88 (by decide) (by decide)).trans (by simp [hat, hsign]))
  obtain ⟨t, et, htt, htm, htf⟩ := SourceCircuit.natField_executes 12 88 (by decide)
    input tape z.natAbs (archive ++ [decide (z<0)]) c hc12' hc88
  refine ⟨t, ?_, ?_, ?_, by simp [htt], ?_⟩
  · convert ea.seq (eb'.seq (ec'.seq et)) using 1 <;> first | rfl | omega
  · simp [htt, Codec.int, List.append_assoc]
  · refine ⟨origin+z.natAbs.bits.length, ?_⟩
    simpa [htt, c, Store.ofState] using (hcf.2.2.2.2.2.1 4 (by decide) (by decide)).trans hb4
  · refine ⟨htf.inputHead.trans (hcf.2.1.trans (hbf.2.1.trans haf.2.1)),
      htm.trans (hcf.2.2.1.trans (hbf.2.2.1.trans haf.2.2.1)),
      htf.randomCursor.trans (hcf.2.2.2.1.trans (hbf.2.2.2.1.trans haf.2.2.2.1)),
      htf.output.trans (hcf.2.2.2.2.1.trans (hbf.2.2.2.2.1.trans haf.2.2.2.2.1)), ?_⟩
    intro i hi
    simp only [logWork, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp only [htt, Function.update_of_ne hi.2.2, Function.update_of_ne hi.2.1]
    exact (hcf.2.2.2.2.2.1 i hi.2.1 hi.2.1).trans
        ((hbf.2.2.2.2.2.1 i hi.1 hi.2.1).trans (haf.2.2.2.2.2.1 i hi.2.2 hi.2.2))

end Maxwell.Cost.NormalizeSource.Rhs
