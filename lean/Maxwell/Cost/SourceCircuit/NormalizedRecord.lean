import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.LogNat
import Maxwell.Logical.DyadicCompile

namespace Maxwell.Cost.SourceCircuit
open Structured
open RationalAccumulator (Blank)

theorem natField_executes (source archive : ℕ) (hne : source ≠ archive)
    (input : List Bool) (randomTape : ℕ → Bool) (n : ℕ) (preceding : List Bool)
    (s : Store) (hs : s.val.tapes source = BitTape.atEnd n.bits)
    (ha : s.val.tapes archive = BitTape.atEnd preceding) :
    ∃ t, Executes input randomTape (.call (LogNat.program source archive))
        (28*n.bits.length+31) s t ∧
      t.val.tapes = Function.update (Function.update s.val.tapes source BitTape.blank)
        archive (BitTape.atEnd (preceding ++ Codec.nat n)) ∧
      t.val.memory = s.val.memory ∧ Frame {source,archive} s.val t.val := by
  let t := Store.ofState (LogNat.finish source archive n.bits preceding s.val)
  have hf := LogNat.finish_frame source archive n.bits preceding s.val
  refine ⟨t,.call _ s _ _ (LogNat.steps source archive hne input randomTape n.bits preceding
    s.val s.property hs ha) rfl,?_,rfl,?_⟩
  · funext j
    by_cases hja : j = archive
    · subst j
      simpa [t,Store.ofState,LogNat.word_bits] using
        LogNat.finish_target source archive hne n.bits preceding s.val
    · by_cases hjs : j = source
      · subst j
        simpa [t,Store.ofState,hja] using LogNat.finish_source source archive n.bits preceding s.val
      · simpa [t,Store.ofState,hja,hjs] using hf.2.2.2.2.2.1 j hjs hja
  · refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
    · intro j _ hj
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
      exact hf.2.2.2.2.2.1 j hj.1 hj.2
    · exact hf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega) (by omega)
    · intro j hj
      exact hf.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega) (by omega)

def normalizedRecord (row column : ℕ) (negative : Bool) (bits : List Bool) : List Bool :=
  Codec.nat row ++ Codec.nat column ++ [negative] ++ bits

def normalizedRecordCode : Code :=
  .seq (.call (LogNat.program 15 85))
    (.seq (.call (LogNat.program 16 85))
      (.seq (appendBitCode 85 23)
        (.seq (appendCode 83 85) (.call (TapeOps.clear 83)))))

def recordWork : Finset ℕ := {15,16,83,85}

/-- Serialize the actual normalized coefficient word after its row and
column, retain its sign, and reclaim all three consumed field tapes. -/
theorem normalizedRecord_executes (input : List Bool) (randomTape : ℕ → Bool)
    (row column : ℕ) (negative : Bool) (bits preceding : List Bool) (origin : ℤ)
    (s : Store) (hrow : s.val.tapes 15 = BitTape.atEnd row.bits)
    (hcolumn : s.val.tapes 16 = BitTape.atEnd column.bits)
    (hbits : s.val.tapes 83 = BitTape.shifted bits origin)
    (hsign : s.val.registers 23 = negative) (hlog : s.val.tapes 85 = BitTape.atEnd preceding) :
    ∃ t, Executes input randomTape normalizedRecordCode
        (28*(row.bits.length+column.bits.length)+17*bits.length+80) s t ∧
      t.val.tapes 85 = BitTape.atEnd (preceding ++ normalizedRecord row column negative bits) ∧
      t.val.tapes 15 = BitTape.blank ∧ t.val.tapes 16 = BitTape.blank ∧
      t.val.tapes 83 = {BitTape.blank with head := origin+bits.length} ∧
      t.val.memory = s.val.memory ∧ Frame recordWork s.val t.val ∧
      (∀ j ∉ recordWork, t.val.tapes j = s.val.tapes j) := by
  obtain ⟨r,er,rt,rm,rf⟩ := natField_executes 15 85 (by omega) input randomTape row preceding s hrow hlog
  obtain ⟨c,ec,ct,cm,cf⟩ := natField_executes 16 85 (by omega) input randomTape column
    (preceding ++ Codec.nat row) r (by simpa [rt] using hcolumn) (by simp [rt])
  obtain ⟨g,eg,gt,gr,gf⟩ := appendBit_executes 85 23 input randomTape
    (preceding ++ Codec.nat row ++ Codec.nat column) c (by simp [ct])
  have csign : c.val.registers 23 = negative := cf.sign.trans (rf.sign.trans hsign)
  obtain ⟨b,eb,bt,bf⟩ := append_executes 83 85 (by omega) input randomTape bits
    (preceding ++ Codec.nat row ++ Codec.nat column ++ [negative]) origin g
    (by simpa [gt,ct,rt] using hbits) (by simp [gt,csign])
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 83 input randomTape bits origin b
    (by simpa [bt,gt,ct,rt] using hbits)
  have keep : ∀ j ∉ recordWork, t.val.tapes j = s.val.tapes j := by
    intro j hj
    simp only [recordWork,Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    simp [tt,bt,gt,ct,rt,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2]
  refine ⟨t,?_,?_,?_,?_,?_,tf.2.2.1.trans (bf.2.2.1.trans (gf.2.2.1.trans (cm.trans rm))),
    ?_,keep⟩
  · convert er.seq (ec.seq (eg.seq (eb.seq et))) using 1 <;> first | rfl | omega
  · simp [tt,bt,normalizedRecord,List.append_assoc]
  · simp [tt,bt,gt,ct,rt]
  · simp [tt,bt,gt,ct]
  · simp [tt]
  · refine ⟨tf.2.1.trans (bf.2.1.trans (gf.2.1.trans (cf.inputHead.trans rf.inputHead))),
      tf.2.2.2.1.trans (bf.2.2.2.1.trans (gf.2.2.2.1.trans (cf.randomCursor.trans rf.randomCursor))),
      tf.2.2.2.2.1.trans (bf.2.2.2.2.1.trans (gf.2.2.2.2.1.trans (cf.output.trans rf.output))),
      fun j _ hj => keep j hj,?_,?_⟩
    · exact (tf.2.2.2.2.2.2 23 (by omega) (by omega)).trans
        ((bf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)).trans
          (congrFun gr 23 |>.trans (cf.sign.trans rf.sign)))
    · intro j hj
      exact (tf.2.2.2.2.2.2 j (by omega) (by omega)).trans
        ((bf.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)).trans
          (congrFun gr j |>.trans ((cf.control j hj).trans (rf.control j hj))))

theorem normalizedRecord_horner_length (row column precision magnitude : ℕ) (negative : Bool) :
    (normalizedRecord row column negative (Logical.Horner.encode precision magnitude)).length =
      (Codec.nat row).length + (Codec.nat column).length + 1 + precision := by
  simp only [normalizedRecord,List.length_append,List.length_singleton,Logical.Horner.encode_length]

end Maxwell.Cost.SourceCircuit
