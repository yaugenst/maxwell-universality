import Maxwell.Cost.PositiveGraph.Endpoints
import Maxwell.Cost.PositiveGraph.TripleScatter
import Maxwell.Cost.SourceCircuit.TraceBinding
import Maxwell.Cost.Subtraction

namespace Maxwell.Cost.PositiveGraph

def rowIndex (dimension count : ℕ) (e : Logical.RationalCode.Entry) (hr : e.row < dimension) :
    Fin (2*dimension+count) := ⟨e.row,by omega⟩
def columnIndex (dimension count : ℕ) (e : Logical.RationalCode.Entry) (hc : e.column < dimension) :
    Fin (2*dimension+count) := ⟨dimension+e.column,by omega⟩
def mediatorIndex (dimension count index : ℕ) (hi : index < count) :
    Fin (2*dimension+count) := ⟨2*dimension+index,by omega⟩

def codeAt {n : ℕ} (words : Vector (List Bool) n) (i : Fin n) : ℕ := addressValue (words.get i)

theorem codeAt_lt {n : ℕ} (words : Vector (List Bool) n) (i : Fin n)
    (h : (words.get i).length = 4) : codeAt words i < 16 := by
  simpa [codeAt,h] using Subtraction.addressValue_lt_pow_length (words.get i)

theorem codeAt_word {n : ℕ} (words : Vector (List Bool) n) (i : Fin n)
    (h : (words.get i).length = 4) : words.get i = FixedWidth.bits 4 (codeAt words i).bits :=
  SourceCircuit.fixedWidth_eq h rfl

def nextEndpoints (width dimension count index : ℕ) (hi : index < count)
    (e : Logical.RationalCode.Entry) (words : Vector (List Bool) (4*count)) : Vector (List Bool) (4*count) :=
  Endpoints.setPair (width+3) (2*(count+index)) (by omega)
    (dimension+e.column).bits (2*dimension+index).bits
    (Endpoints.setPair (width+3) (2*index) (by omega)
      (SourceCircuit.fixedWidth width e.row) (2*dimension+index).bits words)

def nextDiagonal (dimension count index : ℕ) (hi : index < count)
    (e : Logical.RationalCode.Entry) (hr : e.row < dimension) (hc : e.column < dimension)
    (words : Vector (List Bool) (2*dimension+count)) : Vector (List Bool) (2*dimension+count) :=
  let r := rowIndex dimension count e hr
  let c := columnIndex dimension count e hc
  let m := mediatorIndex dimension count index hi
  TripleScatter.updated words r c m (codeAt words r) (codeAt words c) (codeAt words m)
    (decide (e.value<0)) (decide (e.value=1/2 ∨ e.value= -1/2))

def entryMemory (width dimension count index base : ℕ) (hi : index < count)
    (e : Logical.RationalCode.Entry) (hr : e.row < dimension) (hc : e.column < dimension)
    (diagonal : Vector (List Bool) (2*dimension+count)) (memory : ℕ → Bool) : ℕ → Bool :=
  TripleScatter.write base e.row (dimension+e.column) (2*dimension+index)
    (codeAt diagonal (rowIndex dimension count e hr))
    (codeAt diagonal (columnIndex dimension count e hc))
    (codeAt diagonal (mediatorIndex dimension count index hi))
    (decide (e.value<0)) (decide (e.value=1/2 ∨ e.value= -1/2))
    (Endpoints.writePair (width+3) (2*(count+index))
      (dimension+e.column).bits (2*dimension+index).bits
      (Endpoints.writePair (width+3) (2*index) (SourceCircuit.fixedWidth width e.row)
        (2*dimension+index).bits memory))

end Maxwell.Cost.PositiveGraph
