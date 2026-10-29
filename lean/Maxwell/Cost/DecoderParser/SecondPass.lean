import Maxwell.Cost.DecoderParser.Target
import Maxwell.Cost.DecoderParser.ReadFields

namespace Maxwell.Cost.DecoderParser
open Structured

abbrev beforeRowsShape : Shape := .pair .nat (.pair physicalPrefixShape
  (.pair .nat (.pair .nat (.list edgeShape))))

def beforeRowsPayload {n : ℕ} (I : Target.Instance n) : Payload beforeRowsShape :=
  (n,physicalPrefix I,I.decoder.format.integerBits,I.decoder.format.fractionalBits,
    coordinatePayload I.decoder)

def beforeRows {n : ℕ} (I : Target.Instance n) : List Bool :=
  wire beforeRowsShape (beforeRowsPayload I)

theorem target_beforeRows {n : ℕ} (I : Target.Instance n) :
    Codec.target I = beforeRows I ++ Codec.list (wire rowShape) (rowPayload I.decoder) := by
  rw [target_parts]
  simp [beforeRows,beforeRowsPayload,wire,List.append_assoc]

/-- After the one physical input rewind, clear the old retained archive and
skip the physical data and coordinate list once. The next unread field is
the row count. No output row rescans this prefix. -/
def secondPassPrefix : Code := .seq (clearWord 18) (parser beforeRowsShape 0)

theorem secondPassPrefix_steps {n : ℕ} (I : Target.Instance n) (suffix : List Bool)
    (randomTape : ℕ → Bool) (s : Store) (hh : s.val.inputHead=0) (hr : Ready 0 s.val)
    (hlog : s.val.tapes 18 = BitTape.ofList (Codec.target I)) :
    ∃ (cost : ℕ) (t : Store),
      Executes (Codec.target I ++ suffix) randomTape secondPassPrefix cost s t ∧
      cost ≤ 11*(Codec.target I).length+10+price beforeRowsShape (beforeRowsPayload I) ∧
      t.val.inputHead = (beforeRows I).length ∧
      t.val.tapes 18 = BitTape.atEnd (beforeRows I) ∧
      Ready 0 t.val ∧ Frame {18} s.val t.val := by
  obtain ⟨u,hu,hu18,huh,huf⟩ := clearWord_steps 18 (Codec.target I ++ suffix) randomTape
    (Codec.target I) s hlog
  have hur := hr.frame huf
  obtain ⟨a,t,ht,hc,hth,htl,htf⟩ := parser_correct beforeRowsShape 0 (by decide)
    (beforeRowsPayload I) [] (Codec.list (wire rowShape) (rowPayload I.decoder) ++ suffix) []
    randomTape u (by simp [huh,hh]) hur (by simpa [BitTape.atEnd_nil] using hu18)
  have hi : [] ++ (wire beforeRowsShape (beforeRowsPayload I) ++
      (Codec.list (wire rowShape) (rowPayload I.decoder) ++ suffix)) = Codec.target I ++ suffix := by
    simp [target_beforeRows,beforeRows,List.append_assoc]
  rw [hi] at ht
  refine ⟨_,t,hu.seq ht,by omega,?_,by simpa [beforeRows] using htl,hur.frame htf,huf.trans htf⟩
  simpa [huh,hh,beforeRows] using hth

end Maxwell.Cost.DecoderParser
