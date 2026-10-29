import Maxwell.Cost.ZeroSource.Format
import Maxwell.Cost.EmitRepeated
import Maxwell.Cost.EmitNatural

namespace Maxwell.Cost.ZeroSource
open Structured

/-- Dimension metadata is read from tape 19; the loop counter is a private
copy on tape 90. The target header and empty row are fixed literal strings. -/
def emitCode : Code :=
  Code.seq (.call (WordTransfer.clone 19 90)) <|
  Code.seq (EmitNatural.code 19) <|
  Code.seq (EmitLiteral.code 30 header) <|
  Code.seq (EmitNatural.code 19) <|
  EmitRepeated.code 90 row

def emitBound (n : ℕ) : ℕ :=
  (n+1)*(70*n.bits.length+4*row.length+100)+4*header.length+1

theorem emit_steps (n : ℕ) (dimensionOrigin counterOrigin : ℤ)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hn : s.val.tapes 19 = BitTape.shifted n.bits dimensionOrigin)
    (hc : s.val.tapes 90 = {BitTape.blank with head := counterOrigin}) :
    ∃ cost, ∃ t : Store, Executes input randomTape emitCode cost s t ∧
      cost ≤ emitBound n ∧ t.val.output = (targetBits n).reverse ++ s.val.output ∧
      t.val.randomCursor = s.val.randomCursor := by
  obtain ⟨copied, hcopy, hpc, h19, h90, hf⟩ := WordTransfer.clone_steps 19 90 (by decide)
    input randomTape n.bits dimensionOrigin counterOrigin s.val s.property hn hc
  let a := Store.ofState copied
  have ea : Executes input randomTape (.call (WordTransfer.clone 19 90))
      (15*n.bits.length+17) s a := Executes.call _ _ _ _ hcopy
    (by simp [WordTransfer.clone, hpc, Copy.program, Rewind.program, BitRAMInstruction.relocate])
  obtain ⟨b, eb, hbo, hbf⟩ := EmitNatural.executes 19 n dimensionOrigin input randomTape a h19
  let c := EmitLiteral.finish 30 header b
  have ec := EmitLiteral.executes 30 header input randomTape b
  have hcf := EmitLiteral.finish_frame 30 header b
  have hco := EmitLiteral.finish_output 30 header b
  have hc19 : c.val.tapes 19 = BitTape.shifted n.bits dimensionOrigin :=
    (congrFun hcf.2.2.2.2.1 19).trans ((congrFun hbf.2.2.2.2 19).trans h19)
  obtain ⟨d, ed, hdo, hdf⟩ := EmitNatural.executes 19 n dimensionOrigin input randomTape c hc19
  have hd90 : d.val.tapes 90 = BitTape.shifted n.bits counterOrigin :=
    (congrFun hdf.2.2.2.2 90).trans ((congrFun hcf.2.2.2.2.1 90).trans
      ((congrFun hbf.2.2.2.2 90).trans h90))
  obtain ⟨last, t, et, hlast, hto, htr⟩ := EmitRepeated.executes 90 n row counterOrigin
    input randomTape d hd90
  refine ⟨(15*n.bits.length+17)+((20*n.bits.length+24)+((4*header.length+1)+
    ((20*n.bits.length+24)+last))), t, ea.seq (eb.seq (ec.seq (ed.seq et))), ?_, ?_, ?_⟩
  · unfold emitBound
    nlinarith
  · have hao : a.val.output = s.val.output := hf.2.2.2.2.1
    rw [hto, hdo, hco, hbo, hao]
    simp [targetBits, List.reverse_append, List.append_assoc]
  · exact htr.trans (hdf.2.2.2.1.trans (hcf.2.2.2.1.trans
      (hbf.2.2.2.1.trans hf.2.2.2.1)))

end Maxwell.Cost.ZeroSource
