import Maxwell.Cost.PositiveGraph.Initialize.Fill
import Maxwell.Cost.PositiveGraph.Metadata.Plan

namespace Maxwell.Cost.PositiveGraph.Initialize
open RationalAccumulator (Word Blank)

def endpointPorts : Ports := ⟨140,151,146,142,by intro i hi; simp at hi; omega⟩
def counterPorts : Ports := ⟨149,143,150,141,by intro i hi; simp at hi; omega⟩
def rankPorts : Ports := ⟨149,144,150,142,by intro i hi; simp at hi; omega⟩
def diagonalPorts : Ports := ⟨147,145,148,141,by intro i hi; simp at hi; omega⟩

structure Config (W d K value : ℕ) (clock : List Bool) (s : BitRAMState) : Prop where
  numeric : Metadata.Numeric W d K s
  clockWord : BankArray.Word s 146 clock
  scratch : BankArray.Scratch s
  seven : Blank s 7
  temporary : Blank s 37
  cursor : Blank s 160
  count : Blank s 161
  valueWord : Word s 162 value

structure Bounds (W d K B : ℕ) : Prop where
  four : 4 ≤ B
  width : W+3 ≤ B
  widthBits : (W+3).bits.length ≤ B
  counterBase : (4*K*(W+3)).bits.length ≤ B
  rankBase : (4*K*(W+3)+2*(2*d+K)).bits.length ≤ B
  diagonalBase : (4*K*(W+3)+2*(2*d+K)+2*(4*K)).bits.length ≤ B
  verticesBits : (2*d+K).bits.length ≤ B
  incidencesBits : (4*K).bits.length ≤ B
  vertices : 2*d+K < 2^B
  incidences : 4*K < 2^B

theorem Frame.numeric {s t : BitRAMState} (hf : Frame s t) (W d K : ℕ)
    (h : Metadata.Numeric W d K s) : Metadata.Numeric W d K t := by
  have keep (i : ℕ) (hi : 140 ≤ i) (hj : i ≤ 159) : t.tapes i=s.tapes i :=
    hf.tapes i (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.widthWord
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.vertices
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.incidences
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.counterBase
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.rankBase
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.diagonalBase
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.four
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.clockFour
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.two
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.clockTwo
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.endpointBase
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.edges
  | exact RationalAccumulator.word_of_eq (keep _ (by omega) (by omega)) h.doubledDimension
  | exact fun i hi hj => RationalAccumulator.blank_of_eq (keep i (by omega) hj) (h.temporary i hi hj)

theorem Config.after_fill {W d K value : ℕ} {clock : List Bool} {s t : BitRAMState}
    (h : Config W d K value clock s) (p : Ports) (w b c : List Bool)
    (hr : Ready p w b c value t) (hc : Blank t 160) (hn : Blank t 161) (hf : Frame s t) :
    Config W d K value clock t :=
  ⟨hf.numeric W d K h.numeric,
    BankArray.word_of_eq (hf.tapes 146 (by omega) (by omega) (by omega) (by omega) (by omega)) h.clockWord,
    hr.scratch,hr.seven,hr.temporary,hc,hn,hr.valueWord⟩

theorem Config.endpoint {W d K value : ℕ} {clock : List Bool} {s : BitRAMState}
    (h : Config W d K value clock s) : Ready endpointPorts (W+3).bits (0:ℕ).bits clock value s :=
  ⟨h.scratch,h.seven,h.temporary,h.numeric.widthWord,h.numeric.endpointBase,h.clockWord,h.valueWord⟩

theorem Config.counter {W d K value : ℕ} {clock : List Bool} {s : BitRAMState}
    (h : Config W d K value clock s) : Ready counterPorts (2:ℕ).bits (4*K*(W+3)).bits (2:ℕ).bits value s :=
  ⟨h.scratch,h.seven,h.temporary,h.numeric.two,h.numeric.counterBase,h.numeric.clockTwo,h.valueWord⟩

theorem Config.rank {W d K value : ℕ} {clock : List Bool} {s : BitRAMState}
    (h : Config W d K value clock s) : Ready rankPorts (2:ℕ).bits (4*K*(W+3)+2*(2*d+K)).bits (2:ℕ).bits value s :=
  ⟨h.scratch,h.seven,h.temporary,h.numeric.two,h.numeric.rankBase,h.numeric.clockTwo,h.valueWord⟩

theorem Config.diagonal {W d K value : ℕ} {clock : List Bool} {s : BitRAMState}
    (h : Config W d K value clock s) : Ready diagonalPorts (4:ℕ).bits
      (4*K*(W+3)+2*(2*d+K)+2*(4*K)).bits (8:ℕ).bits value s :=
  ⟨h.scratch,h.seven,h.temporary,h.numeric.four,h.numeric.diagonalBase,h.numeric.clockFour,h.valueWord⟩

end Maxwell.Cost.PositiveGraph.Initialize
