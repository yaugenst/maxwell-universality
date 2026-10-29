import Maxwell.Cost.PositiveGraph.Initialize.FillConfig
import Maxwell.Cost.PositiveGraph.Initialize.Regions

namespace Maxwell.Cost.PositiveGraph.Initialize
open Structured

abbrev constantWords (n width value : ℕ) : Vector (List Bool) n :=
  Vector.ofFn fun _ => FixedWidth.bits width value.bits

structure ZeroArrays (W d K : ℕ) (memory : ℕ → Bool) : Prop where
  endpoints : BitArray.Represents memory 0 (W+3) (constantWords (4*K) (W+3) 0)
  counters : BitArray.Represents memory (4*K*(W+3)) 2 (constantWords (2*d+K) 2 0)
  ranks : BitArray.Represents memory (4*K*(W+3)+2*(2*d+K)) 2 (constantWords (4*K) 2 0)

def zeroCode : Code := .seq (fillCode endpointPorts) (.seq (fillCode counterPorts) (fillCode rankPorts))
def zeroCost (d K B : ℕ) : ℕ := 66000*(4*K+(2*d+K)+1)*(B+2)^2

theorem zero_executes (W d K B : ℕ) (clock : List Bool) (hc : clock.length=W+3)
    (hb : Bounds W d K B) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Config W d K 0 clock s.val) :
    ∃ cost t, cost ≤ zeroCost d K B ∧ Executes input tape zeroCode cost s t ∧
      Config W d K 0 clock t.val ∧ ZeroArrays W d K t.val.memory ∧
      Outside 0 (4*K*(W+3)+2*(2*d+K)+2*(4*K)) 1 s.val t.val ∧ Frame s.val t.val := by
  have hfour := hb.four
  obtain ⟨ca,a,hca,ea,ha,aa,ao,af⟩ := fill_config endpointPorts (W+3) 0 (4*K) B clock
    hb.widthBits (by simp) hb.incidencesBits (by omega) hb.width hc (by simp)
    hb.incidences input tape s hs hs.numeric.widthWord hs.numeric.endpointBase hs.clockWord hs.numeric.incidences
  obtain ⟨cb,b,hcb,eb,hbconfig,ba,bo,bf⟩ := fill_config counterPorts 2 (4*K*(W+3)) (2*d+K) B (2:ℕ).bits
    (by change 2 ≤ B; omega) hb.counterBase hb.verticesBits (by omega) (by omega)
    rfl (by decide) hb.vertices input tape a ha ha.numeric.two ha.numeric.counterBase ha.numeric.clockTwo ha.numeric.vertices
  obtain ⟨ct,t,hct,et,ht,ta,hto,tf⟩ := fill_config rankPorts 2 (4*K*(W+3)+2*(2*d+K)) (4*K) B (2:ℕ).bits
    (by change 2 ≤ B; omega) hb.rankBase hb.incidencesBits (by omega) (by omega)
    rfl (by decide) hb.incidences input tape b hbconfig hbconfig.numeric.two hbconfig.numeric.rankBase
    hbconfig.numeric.clockTwo hbconfig.numeric.incidences
  have aab : BitArray.Represents b.val.memory 0 (W+3) (constantWords (4*K) (W+3) 0) :=
    bo.preserves_before (by omega) aa
  have aat : BitArray.Represents t.val.memory 0 (W+3) (constantWords (4*K) (W+3) 0) :=
    hto.preserves_before (by omega) aab
  have bat : BitArray.Represents t.val.memory (4*K*(W+3)) 2 (constantWords (2*d+K) 2 0) :=
    hto.preserves_before (by omega) ba
  refine ⟨ca+(cb+ct),t,?_,ea.seq (eb.seq et),ht,⟨aat,bat,ta⟩,
    (ao.widen (by omega)).trans ((bo.widen (by omega)).trans (hto.widen (by omega))),
    af.trans (bf.trans tf)⟩
  dsimp [fillCost] at hca hcb hct
  dsimp [zeroCost]
  nlinarith

end Maxwell.Cost.PositiveGraph.Initialize
