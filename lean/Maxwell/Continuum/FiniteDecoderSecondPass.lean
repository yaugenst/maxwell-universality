import Maxwell.Continuum.FiniteDecoderMetadata
import Maxwell.Cost.DecoderParser.ReadFields

namespace Maxwell.Continuum.FiniteDecoder
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.DecoderParser

/-- After the input rewind, clear the old retained archive and
parse the four scalar decoder metadata fields once. The next unread field is
the row count. No output row rescans this prefix. -/
def secondPassPrefix : Code := .seq (clearWord 18) (parser headerShape 0)

theorem secondPassPrefix_steps {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (suffix : List Bool)
    (randomTape : ℕ → Bool) (s : Store) (hh : s.val.inputHead=0) (hr : Ready 0 s.val)
    (hlog : s.val.tapes 18 = BitTape.ofList (description D)) :
    ∃ (cost : ℕ) (t : Store),
      Executes (description D ++ suffix) randomTape secondPassPrefix cost s t ∧
      cost ≤ 11*(description D).length+10+price headerShape (headerData D) ∧
      t.val.inputHead = (beforeRows D).length ∧
      t.val.tapes 18 = BitTape.atEnd (beforeRows D) ∧
      Ready 0 t.val ∧ Frame {18} s.val t.val := by
  obtain ⟨u,hu,hu18,huh,huf⟩ := clearWord_steps 18 (description D ++ suffix) randomTape
    (description D) s hlog
  have hur := hr.frame huf
  obtain ⟨a,t,ht,hc,hth,htl,htf⟩ := parser_correct headerShape 0 (by decide)
    (headerData D) [] (Codec.list (wire rowShape) (rowData D) ++ suffix) []
    randomTape u (by simp [huh,hh]) hur (by simpa [BitTape.atEnd_nil] using hu18)
  have hi : [] ++ (wire headerShape (headerData D) ++
      (Codec.list (wire rowShape) (rowData D) ++ suffix)) = description D ++ suffix := by
    simp [description_parts,beforeRows,List.append_assoc]
  rw [hi] at ht
  refine ⟨_,t,hu.seq ht,by omega,?_,by simpa [beforeRows] using htl,hur.frame htf,huf.trans htf⟩
  simpa [huh,hh,beforeRows] using hth

end Maxwell.Continuum.FiniteDecoder

