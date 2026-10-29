import Maxwell.Cost.PositiveGraph.Initialize.Zeros
import Maxwell.Cost.PositiveGraph.Initialize.Constants

namespace Maxwell.Cost.PositiveGraph.Initialize
open Structured

structure Arrays (W d K : ℕ) (memory : ℕ → Bool) : Prop extends ZeroArrays W d K memory where
  diagonals : BitArray.Represents memory (4*K*(W+3)+2*(2*d+K)+2*(4*K)) 4
    (constantWords (2*d+K) 4 8)

def memoryEnd (W d K : ℕ) : ℕ := 4*K*(W+3)+2*(2*d+K)+2*(4*K)+4*(2*d+K)
def code : Code := .seq zeroCode (.seq eightCode (.seq (fillCode diagonalPorts) (.call (TapeOps.clear 162))))
def costCap (d K B : ℕ) : ℕ := 100000*(4*K+(2*d+K)+1)*(B+2)^2

theorem executes (W d K B : ℕ) (clock : List Bool) (hc : clock.length=W+3)
    (hb : Bounds W d K B) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Config W d K 0 clock s.val) :
    ∃ cost t, cost ≤ costCap d K B ∧ Executes input tape code cost s t ∧
      Config W d K 0 clock t.val ∧ Arrays W d K t.val.memory ∧
      Outside 0 (memoryEnd W d K) 1 s.val t.val ∧ Frame s.val t.val := by
  have hfour := hb.four
  obtain ⟨ca,a,hca,ea,ha,aa,ao,af⟩ := zero_executes W d K B clock hc hb input tape s hs
  obtain ⟨b,eb,hbconfig,bm,bf⟩ := ha.eight input tape a
  obtain ⟨cc,c,hcc,ec,hcconfig,ac,co,cf⟩ := fill_config diagonalPorts 4
    (4*K*(W+3)+2*(2*d+K)+2*(4*K)) (2*d+K) B (8:ℕ).bits
    (by change 3 ≤ B; omega) hb.diagonalBase hb.verticesBits (by omega) hb.four
    rfl (by decide) hb.vertices input tape b hbconfig hbconfig.numeric.four hbconfig.numeric.diagonalBase
    hbconfig.numeric.clockFour hbconfig.numeric.vertices
  obtain ⟨t,et,ht,tm,tf⟩ := hcconfig.clear input tape c
  have az : ZeroArrays W d K b.val.memory := by simpa only [bm] using aa
  have tz : ZeroArrays W d K t.val.memory := by
    rw [tm]
    exact ⟨co.preserves_before (by omega) az.endpoints,
      co.preserves_before (by omega) az.counters,co.preserves_before (by omega) az.ranks⟩
  refine ⟨ca+(46+(cc+28)),t,?_,ea.seq (eb.seq (ec.seq et)),ht,
    ⟨tz,by simpa only [tm] using ac⟩,
    (ao.widen (by dsimp [memoryEnd]; omega)).trans
      ((Outside.of_memory bm).trans ((co.widen (by dsimp [memoryEnd]; omega)).trans (Outside.of_memory tm))),
    af.trans (bf.trans (cf.trans tf))⟩
  dsimp [zeroCost] at hca
  dsimp [fillCost] at hcc
  dsimp [costCap]
  have hq : 4 ≤ (B+2)^2 := by nlinarith
  nlinarith

def program : BitRAM := code.compile

end Maxwell.Cost.PositiveGraph.Initialize
