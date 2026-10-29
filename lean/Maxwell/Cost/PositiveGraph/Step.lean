import Maxwell.Cost.PositiveGraph.EntryEndpoints
import Maxwell.Cost.PositiveGraph.Cleanup
import Maxwell.Cost.PositiveGraph.Data

namespace Maxwell.Cost.PositiveGraph.Step
open Structured

def code : Code := .seq EntryEndpoints.code
  (.seq TripleScatter.code (.seq (BankArray.incrementCode 121) Cleanup.code))

def price (width dimension count index base : ℕ) (e : Logical.RationalCode.Entry)
    (clock : List Bool) (rv cv mv : ℕ) : ℕ :=
  EntryEndpoints.price width dimension count index e+
    TripleScatter.costCap (SourceCircuit.fixedWidth width e.row) (dimension+e.column).bits
      (2*dimension+index).bits clock base rv cv mv
      (decide (e.value<0)) (decide (e.value=1/2 ∨ e.value= -1/2))+
    12*(2*dimension+index).bits.length+18+22*width+6*(dimension+e.column).bits.length+24

/-- One actual sparse record emits four graph endpoints and scatters the
three exact half-integer diagonal contributions, reclaiming parser scratch. -/
theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (width dimension count index base : ℕ) (e : Logical.RationalCode.Entry)
    (sourceClock endpointClock diagonalClock suffix : List Bool) (s : Store)
    (hindex : index < count) (hcount : count ≤ 3*dimension) (hdimension : dimension < 2^width)
    (hrow : e.row < dimension) (hcolumn : e.column < dimension)
    (hsep : 4*count*(width+3) ≤ base)
    (hd : Descriptor width dimension base sourceClock endpointClock diagonalClock s.val)
    (hc : Cursors dimension count index s.val) (hw : Workspace s.val)
    (endpoints : Vector (List Bool) (4*count)) (diagonal : Vector (List Bool) (2*dimension+count))
    (he : BitArray.Represents s.val.memory 0 (width+3) endpoints)
    (hg : BitArray.Represents s.val.memory base 4 diagonal)
    (hsource : TapeRepresents (s.val.tapes 110) (SparseEmission.entryWire width e++suffix)) :
    ∃ cost t, cost ≤ price width dimension count index base e diagonalClock
        (codeAt diagonal (rowIndex dimension count e hrow))
        (codeAt diagonal (columnIndex dimension count e hcolumn))
        (codeAt diagonal (mediatorIndex dimension count index hindex)) ∧
      Executes input randomTape code cost s t ∧
      t.val.tapes 110 = SparseEmission.ReadGate.advance (s.val.tapes 110) (2*width+2) ∧
      TapeRepresents (t.val.tapes 110) suffix ∧
      t.val.memory = entryMemory width dimension count index base hindex e hrow hcolumn diagonal s.val.memory ∧
      BitArray.Represents t.val.memory 0 (width+3) (nextEndpoints width dimension count index hindex e endpoints) ∧
      BitArray.Represents t.val.memory base 4 (nextDiagonal dimension count index hindex e hrow hcolumn diagonal) ∧
      Descriptor width dimension base sourceClock endpointClock diagonalClock t.val ∧
      Cursors dimension count (index+1) t.val ∧ Workspace t.val ∧ Frame workBanks s.val t.val := by
  let r := rowIndex dimension count e hrow
  let c := columnIndex dimension count e hcolumn
  let m := mediatorIndex dimension count index hindex
  let rv := codeAt diagonal r
  let cv := codeAt diagonal c
  let mv := codeAt diagonal m
  let negative := decide (e.value<0)
  let half := decide (e.value=1/2 ∨ e.value= -1/2)
  obtain ⟨ac,a,acBound,ea,a110,asuffix,am,ae,ao,af⟩ := EntryEndpoints.executes input randomTape
    width dimension count index base e sourceClock endpointClock diagonalClock suffix s
    hindex hcount hdimension hrow hcolumn hd hc hw endpoints he hsource
  have ag : BitArray.Represents a.val.memory base 4 diagonal := by
    rw [am]
    exact Endpoints.writePair_preserves (m := 4*count)
      (Endpoints.writePair_preserves (m := 4*count) hg (width+3) (2*index) (by omega)
        (SourceCircuit.fixedWidth width e.row) (2*dimension+index).bits (Or.inr (by omega)))
      (width+3) (2*(count+index)) (by omega) (dimension+e.column).bits (2*dimension+index).bits
      (Or.inr (by omega))
  have hrc : r ≠ c := by intro h; have := congrArg Fin.val h; dsimp [r,c,rowIndex,columnIndex] at this; omega
  have hrm : r ≠ m := by intro h; have := congrArg Fin.val h; dsimp [r,m,rowIndex,mediatorIndex] at this; omega
  have hcm : c ≠ m := by intro h; have := congrArg Fin.val h; dsimp [c,m,columnIndex,mediatorIndex] at this; omega
  obtain ⟨bc,b,bcBound,eb,bm,bg,bscratch,b7,b120,_bn,_bh,_brole,bf⟩ := TripleScatter.executes
    input randomTape (SourceCircuit.fixedWidth width e.row) (dimension+e.column).bits
    (2*dimension+index).bits diagonalClock base rv cv mv diagonal r c m
    (SourceCircuit.fixedWidth_value _ _ (by omega)) (RationalAccumulator.address_bits _)
    (RationalAccumulator.address_bits _) hrc hrm hcm ao.descriptor.diagonalClock_length
    (codeAt_lt _ _ (hg.length r)) (codeAt_lt _ _ (hg.length c)) (codeAt_lt _ _ (hg.length m))
    (codeAt_word _ _ (hg.length r)) (codeAt_word _ _ (hg.length c)) (codeAt_word _ _ (hg.length m))
    negative half a ao.scratch ao.sample ao.payload ao.descriptor.diagonalWidth ao.descriptor.diagonalBase
    ao.descriptor.diagonalClock ⟨0,ao.row⟩ ao.shiftedColumn ao.mediator ag ao.negative ao.half
  have bkeep (j : ℕ) (hj : 10 ≤ j) (hj120 : j ≠ 120) : b.val.tapes j = a.val.tapes j :=
    bf.tapes j (Or.inr hj) (by simpa using hj120)
  have be : BitArray.Represents b.val.memory 0 (width+3)
      (nextEndpoints width dimension count index hindex e endpoints) := by
    rw [bm]
    exact TripleScatter.write_preserves ae r c m rv cv mv negative half (Or.inl (by omega))
  obtain ⟨cc,cstate,ccBound,ec,cmWord,cscratch,cmMemory,_ca,ck,cf⟩ := BankArray.increment_bank 121
    (by decide) input randomTape (2*dimension+index).bits b
    (BankArray.word_of_eq (bkeep 121 (by decide) (by decide)) ao.mediator) bscratch
  have cmWord' : BankArray.Word cstate.val 121 (2*dimension+(index+1)).bits := by
    simpa only [PairWrite.increment_bits,Nat.add_assoc] using cmWord
  have c111 : cstate.val.tapes 111 = BitTape.shifted (SourceCircuit.fixedWidth width e.row) 0 :=
    (ck 111 (by decide)).trans ((bkeep 111 (by decide) (by decide)).trans ao.row)
  have c112 : cstate.val.tapes 112 = BitTape.shifted (SourceCircuit.fixedWidth width e.column) 0 :=
    (ck 112 (by decide)).trans ((bkeep 112 (by decide) (by decide)).trans ao.column)
  have c122 : RationalAccumulator.Word cstate.val 122 (dimension+e.column) := BankArray.word_of_eq
    ((ck 122 (by decide)).trans (bkeep 122 (by decide) (by decide))) ao.shiftedColumn
  obtain ⟨t,et,t111,t112,t122,tm,tf,tk⟩ := Cleanup.executes input randomTape
    (SourceCircuit.fixedWidth width e.row) (SourceCircuit.fixedWidth width e.column)
    (dimension+e.column).bits cstate c111 c112 c122
  have t110 : t.val.tapes 110 = a.val.tapes 110 :=
    (tk 110 (by decide) (by decide) (by decide)).trans ((ck 110 (by decide)).trans (bkeep 110 (by decide) (by decide)))
  have finalFrame : Frame workBanks s.val t.val := af.trans ((bf.mono (by decide)).trans
    (((Frame.of_source (SourceCircuit.frame_except cf)).mono (by decide)).trans (tf.mono (by decide))))
  refine ⟨_,t,?_,ea.seq (eb.seq (ec.seq et)),t110.trans a110,t110 ▸ asuffix,?_,?_,?_,
    hd.of_frame finalFrame,?_,?_,finalFrame⟩
  · unfold price
    simp only [SourceCircuit.fixedWidth_length]
    dsimp only [rv,cv,mv,r,c,m,negative,half] at *
    omega
  · rw [tm,cmMemory,bm,am]
    rfl
  · simpa only [tm,cmMemory] using be
  · simpa only [tm,cmMemory,nextDiagonal,r,c,m,rv,cv,mv,negative,half] using bg
  · refine ⟨?_,?_,BankArray.word_of_eq (tk 121 (by decide) (by decide) (by decide)) cmWord'⟩
    · exact BankArray.word_of_eq ((tk 118 (by decide) (by decide) (by decide)).trans
        ((ck 118 (by decide)).trans (bkeep 118 (by decide) (by decide)))) ao.left
    · exact BankArray.word_of_eq ((tk 119 (by decide) (by decide) (by decide)).trans
        ((ck 119 (by decide)).trans (bkeep 119 (by decide) (by decide)))) ao.right
  · refine ⟨SourceCircuit.scratch_of_tapes cscratch (fun j hj => tk j (by omega) (by omega) (by omega)),
      RationalAccumulator.blank_of_eq ((tk 7 (by decide) (by decide) (by decide)).trans (ck 7 (by decide))) b7,
      ?_,RationalAccumulator.blank_of_eq ((tk 120 (by decide) (by decide) (by decide)).trans
        (ck 120 (by decide))) b120,t122,t111,t112⟩
    exact RationalAccumulator.blank_of_eq ((tk 37 (by decide) (by decide) (by decide)).trans
      ((ck 37 (by decide)).trans (bkeep 37 (by decide) (by decide)))) ao.packed

end Maxwell.Cost.PositiveGraph.Step
