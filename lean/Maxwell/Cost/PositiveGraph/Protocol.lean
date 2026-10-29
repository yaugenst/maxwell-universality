import Maxwell.Cost.PositiveGraph.Frame
import Maxwell.Cost.SourceCircuit.Common

namespace Maxwell.Cost.PositiveGraph
open Structured
open RationalAccumulator (Blank)

def metadataBanks : Finset ℕ := {93,95,140,145,146,147,148,151}

structure Descriptor (width dimension diagonalBase : ℕ)
    (sourceClockBits endpointClockBits diagonalClockBits : List Bool) (s : BitRAMState) : Prop where
  sourceClock : BankArray.Word s 93 sourceClockBits
  sourceClock_length : sourceClockBits.length = width
  dimension : BankArray.Word s 95 (SourceCircuit.fixedWidth width dimension)
  endpointWidth : BankArray.Word s 140 (width+3).bits
  endpointClock : BankArray.Word s 146 endpointClockBits
  endpointClock_length : endpointClockBits.length = width+3
  endpointBase : BankArray.Word s 151 []
  diagonalWidth : BankArray.Word s 147 (4:ℕ).bits
  diagonalBase : BankArray.Word s 145 diagonalBase.bits
  diagonalClock : BankArray.Word s 148 diagonalClockBits
  diagonalClock_length : diagonalClockBits.length = 4

theorem Descriptor.transport {width dimension diagonalBase : ℕ}
    {sourceClock endpointClock diagonalClock : List Bool} {s t : BitRAMState}
    (h : Descriptor width dimension diagonalBase sourceClock endpointClock diagonalClock s)
    (ht : ∀ i ∈ metadataBanks, t.tapes i = s.tapes i) :
    Descriptor width dimension diagonalBase sourceClock endpointClock diagonalClock t :=
  ⟨BankArray.word_of_eq (ht 93 (by decide)) h.sourceClock,h.sourceClock_length,
    BankArray.word_of_eq (ht 95 (by decide)) h.dimension,
    BankArray.word_of_eq (ht 140 (by decide)) h.endpointWidth,
    BankArray.word_of_eq (ht 146 (by decide)) h.endpointClock,h.endpointClock_length,
    BankArray.word_of_eq (ht 151 (by decide)) h.endpointBase,
    BankArray.word_of_eq (ht 147 (by decide)) h.diagonalWidth,
    BankArray.word_of_eq (ht 145 (by decide)) h.diagonalBase,
    BankArray.word_of_eq (ht 148 (by decide)) h.diagonalClock,h.diagonalClock_length⟩

structure Cursors (dimension count index : ℕ) (s : BitRAMState) : Prop where
  left : BankArray.Word s 118 (2*index).bits
  right : BankArray.Word s 119 (2*(count+index)).bits
  mediator : BankArray.Word s 121 (2*dimension+index).bits

structure Workspace (s : BitRAMState) : Prop where
  scratch : BankArray.Scratch s
  sample : Blank s 7
  packed : Blank s 37
  payload : Blank s 120
  shiftedColumn : Blank s 122
  row : s.tapes 111 = BitTape.blank
  column : s.tapes 112 = BitTape.blank

def workBanks : Finset ℕ := {37,110,111,112,118,119,120,121,122}

theorem Descriptor.of_frame {width dimension diagonalBase : ℕ}
    {sourceClock endpointClock diagonalClock : List Bool} {s t : BitRAMState}
    (h : Descriptor width dimension diagonalBase sourceClock endpointClock diagonalClock s)
    (hf : Frame workBanks s t) :
    Descriptor width dimension diagonalBase sourceClock endpointClock diagonalClock t := by
  apply h.transport
  intro i hi
  simp only [metadataBanks,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hf.tapes _ (by omega) (by decide)

end Maxwell.Cost.PositiveGraph
