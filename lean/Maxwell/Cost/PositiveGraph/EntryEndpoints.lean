import Maxwell.Cost.PositiveGraph.Protocol
import Maxwell.Cost.PositiveGraph.Column
import Maxwell.Cost.PositiveGraph.Endpoints
import Mathlib.Data.Nat.Size

namespace Maxwell.Cost.PositiveGraph.EntryEndpoints
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq Parse.code (.seq Column.code Endpoints.code)

def price (width dimension count index : ℕ) (e : Logical.RationalCode.Entry) : ℕ :=
  451*width+856+
    PairWrite.price (width+3).bits (2*index) (SourceCircuit.fixedWidth width e.row) (2*dimension+index).bits+
    PairWrite.price (width+3).bits (2*(count+index)) (dimension+e.column).bits (2*dimension+index).bits

structure Output (width dimension count index diagonalBase : ℕ) (e : Logical.RationalCode.Entry)
    (sourceClock endpointClock diagonalClock : List Bool) (s : BitRAMState) : Prop where
  descriptor : Descriptor width dimension diagonalBase sourceClock endpointClock diagonalClock s
  left : BankArray.Word s 118 (2*(index+1)).bits
  right : BankArray.Word s 119 (2*(count+(index+1))).bits
  mediator : BankArray.Word s 121 (2*dimension+index).bits
  row : s.tapes 111 = BitTape.shifted (SourceCircuit.fixedWidth width e.row) 0
  column : s.tapes 112 = BitTape.shifted (SourceCircuit.fixedWidth width e.column) 0
  shiftedColumn : RationalAccumulator.Word s 122 (dimension+e.column)
  scratch : BankArray.Scratch s
  sample : Blank s 7
  packed : Blank s 37
  payload : Blank s 120
  negative : s.registers 44 = decide (e.value < 0)
  half : s.registers 45 = decide (e.value = 1/2 ∨ e.value = -1/2)

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (width dimension count index diagonalBase : ℕ) (e : Logical.RationalCode.Entry)
    (sourceClock endpointClock diagonalClock suffix : List Bool) (s : Store)
    (hindex : index < count) (hcount : count ≤ 3*dimension) (hdimension : dimension < 2^width)
    (hrow : e.row < dimension) (hcolumn : e.column < dimension)
    (hd : Descriptor width dimension diagonalBase sourceClock endpointClock diagonalClock s.val)
    (hc : Cursors dimension count index s.val) (hw : Workspace s.val)
    (words : Vector (List Bool) (4*count))
    (harray : BitArray.Represents s.val.memory 0 (width+3) words)
    (hsource : TapeRepresents (s.val.tapes 110) (SparseEmission.entryWire width e++suffix)) :
    ∃ cost t, cost ≤ price width dimension count index e ∧
      Executes input randomTape code cost s t ∧
      t.val.tapes 110 = SparseEmission.ReadGate.advance (s.val.tapes 110) (2*width+2) ∧
      TapeRepresents (t.val.tapes 110) suffix ∧
      t.val.memory = Endpoints.writePair (width+3) (2*(count+index))
        (dimension+e.column).bits (2*dimension+index).bits
        (Endpoints.writePair (width+3) (2*index) (SourceCircuit.fixedWidth width e.row)
          (2*dimension+index).bits s.val.memory) ∧
      BitArray.Represents t.val.memory 0 (width+3)
        (Endpoints.setPair (width+3) (2*(count+index)) (by omega)
          (dimension+e.column).bits (2*dimension+index).bits
          (Endpoints.setPair (width+3) (2*index) (by omega)
            (SourceCircuit.fixedWidth width e.row) (2*dimension+index).bits words)) ∧
      Output width dimension count index diagonalBase e sourceClock endpointClock diagonalClock t.val ∧
      Frame workBanks s.val t.val := by
  let row := SourceCircuit.fixedWidth width e.row
  let column := SourceCircuit.fixedWidth width e.column
  have rowLength : row.length = width := SourceCircuit.fixedWidth_length _ _
  have columnLength : column.length = width := SourceCircuit.fixedWidth_length _ _
  obtain ⟨clockOrigin,hclock⟩ := hd.sourceClock
  obtain ⟨a,ea,a110,asuffix,a111,a112,aneg,ahalf,af⟩ := Parse.executes input randomTape
    row column sourceClock suffix (decide (e.value<0)) (decide (e.value=1/2 ∨ e.value= -1/2))
    clockOrigin s (columnLength.trans rowLength.symm) (hd.sourceClock_length.trans rowLength.symm)
    (by simpa only [SparseEmission.entryWire,SparseEmission.valueBits,List.append_assoc] using hsource)
    hclock hw.row hw.column
  have aframe : Frame workBanks s.val a.val := (Frame.of_parse af).mono (by decide)
  have ad := hd.of_frame aframe
  have akeep (j : ℕ) (h110 : j ≠ 110) (h111 : j ≠ 111) (h112 : j ≠ 112) :
      a.val.tapes j = s.val.tapes j := af.tapes j h110 h111 h112
  have ascratch := SourceCircuit.scratch_of_tapes hw.scratch
    (fun j hj => akeep j (by omega) (by omega) (by omega))
  obtain ⟨bc,b,bcBound,eb,b122,bscratch,bm,bf,bkeepAll⟩ := Column.executes input randomTape
    (SourceCircuit.fixedWidth width dimension) column a ad.dimension ⟨0,a112⟩
    (RationalAccumulator.blank_of_eq (akeep 122 (by decide) (by decide) (by decide)) hw.shiftedColumn) ascratch
  have hdimValue : addressValue (SourceCircuit.fixedWidth width dimension) = dimension :=
    SourceCircuit.fixedWidth_value _ _ hdimension
  have hcolValue : addressValue column = e.column := SourceCircuit.fixedWidth_value _ _ (by omega)
  have b122' : RationalAccumulator.Word b.val 122 (dimension+e.column) := by simpa only [hdimValue,hcolValue] using b122
  have bframe : Frame workBanks a.val b.val := (Frame.of_source bf).mono (by decide)
  have bd := ad.of_frame bframe
  have bkeep (j : ℕ) (hj : 10 ≤ j) (hj122 : j ≠ 122) : b.val.tapes j = a.val.tapes j :=
    bf.tapes j (Or.inr hj) (by simpa using hj122)
  have b111 : b.val.tapes 111 = BitTape.shifted row 0 := (bkeep 111 (by decide) (by decide)).trans a111
  have b112 : b.val.tapes 112 = BitTape.shifted column 0 := (bkeep 112 (by decide) (by decide)).trans a112
  have bMed : BankArray.Word b.val 121 (2*dimension+index).bits := BankArray.word_of_eq
    ((bkeep 121 (by decide) (by decide)).trans (akeep 121 (by decide) (by decide) (by decide))) hc.mediator
  have bLeft : BankArray.Word b.val 118 (2*index).bits := BankArray.word_of_eq
    ((bkeep 118 (by decide) (by decide)).trans (akeep 118 (by decide) (by decide) (by decide))) hc.left
  have bRight : BankArray.Word b.val 119 (2*(count+index)).bits := BankArray.word_of_eq
    ((bkeep 119 (by decide) (by decide)).trans (akeep 119 (by decide) (by decide) (by decide))) hc.right
  have b7 : Blank b.val 7 := RationalAccumulator.blank_of_eq
    ((bkeepAll 7 (by decide) (by decide)).trans (akeep 7 (by decide) (by decide) (by decide))) hw.sample
  have b37 : Blank b.val 37 := RationalAccumulator.blank_of_eq
    ((bkeep 37 (by decide) (by decide)).trans (akeep 37 (by decide) (by decide) (by decide))) hw.packed
  have hmedFit : (2*dimension+index).bits.length ≤ width+3 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    rw [pow_add]
    norm_num
    omega
  have hcolFit : (dimension+e.column).bits.length ≤ width+3 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    rw [pow_add]
    norm_num
    omega
  obtain ⟨cc,t,ccBound,ec,tm,ta,tLeft,tRight,tscratch,t7,t37,tf⟩ := Endpoints.executes input randomTape
    (width+3).bits endpointClock row (dimension+e.column).bits (2*dimension+index).bits
    (2*index) (2*(count+index)) (by omega) (by omega) words b
    (by rw [Nat.size_eq_bits_len]; exact Nat.size_pos.mpr (by omega))
    (by rw [RationalAccumulator.address_bits]; omega)
    (by simpa only [RationalAccumulator.address_bits] using bd.endpointClock_length)
    (by simpa only [RationalAccumulator.address_bits,rowLength] using Nat.le_add_right width 3)
    (by simpa only [RationalAccumulator.address_bits] using hcolFit)
    (by simpa only [RationalAccumulator.address_bits] using hmedFit)
    bscratch b7 b37 bd.endpointWidth bd.endpointClock bd.endpointBase bLeft bRight ⟨0,b111⟩ b122' bMed
    (by simpa only [RationalAccumulator.address_bits,bm,af.memory] using harray)
  have tframe : Frame workBanks b.val t.val := (Frame.of_source tf).mono (by decide)
  have tkeep (j : ℕ) (hj : 10 ≤ j) (h37 : j ≠ 37) (h118 : j ≠ 118) (h119 : j ≠ 119) :
      t.val.tapes j = b.val.tapes j := tf.tapes j (Or.inr hj) (by simp [h37,h118,h119])
  have t110 : t.val.tapes 110 = a.val.tapes 110 :=
    (tkeep 110 (by decide) (by decide) (by decide) (by decide)).trans (bkeep 110 (by decide) (by decide))
  refine ⟨_,t,?_,ea.seq (eb.seq ec),?_,t110 ▸ asuffix,?_,?_,?_,aframe.trans (bframe.trans tframe)⟩
  · unfold price
    simp only [rowLength,SourceCircuit.fixedWidth_length,columnLength] at bcBound ⊢
    exact Nat.add_le_add_left (Nat.add_le_add bcBound ccBound) _ |>.trans (by
      simp only [row,PairWrite.price,RationalAccumulator.address_bits] at *
      omega)
  · simpa only [rowLength] using t110.trans a110
  · simpa only [RationalAccumulator.address_bits,bm,af.memory] using tm
  · simpa only [RationalAccumulator.address_bits] using ta
  · refine ⟨bd.of_frame tframe,?_,?_,BankArray.word_of_eq
      (tkeep 121 (by decide) (by decide) (by decide) (by decide)) bMed,
      (tkeep 111 (by decide) (by decide) (by decide) (by decide)).trans b111,
      (tkeep 112 (by decide) (by decide) (by decide) (by decide)).trans b112,
      BankArray.word_of_eq (tkeep 122 (by decide) (by decide) (by decide) (by decide)) b122',
      tscratch,t7,t37,?_,?_,?_⟩
    · simpa [Nat.mul_add,Nat.add_assoc] using tLeft
    · simpa [Nat.mul_add,Nat.add_assoc] using tRight
    · exact RationalAccumulator.blank_of_eq
        ((tkeep 120 (by decide) (by decide) (by decide) (by decide)).trans
          ((bkeep 120 (by decide) (by decide)).trans (akeep 120 (by decide) (by decide) (by decide)))) hw.payload
    · exact (tf.control 44 (by decide)).trans ((bf.control 44 (by decide)).trans aneg)
    · exact (tf.control 45 (by decide)).trans ((bf.control 45 (by decide)).trans ahalf)

end Maxwell.Cost.PositiveGraph.EntryEndpoints
