import Maxwell.Continuum.SourceRoutingPathPhaseData

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
open Maxwell.Logical.Routing GeometryPath
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem write_frame (memory : ℕ→Bool) (base offset capacity : ℕ) (bits : List Bool)
    (room : offset+bits.length ≤ capacity) :
    Tree.Memory.Frame base capacity memory (MemoryWord.writeBits memory (base+offset) bits) := by
  intro address outside
  apply MemoryWord.writeBits_outside
  rcases outside with outside|outside
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem Plan.history_frame {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (n : ℕ) {before after : ℕ→Bool}
    (stored : GeometryHistory.Stored p.history initial (2*q) before)
    (frame : Tree.Memory.Frame p.base (n*p.width) before after) :
    GeometryHistory.Stored p.history initial (2*q) after := by
  intro k hk
  apply frame.represents (Or.inl ?_) (stored k hk)
  have bound:=p.history.slab_mono (show k+1 ≤ 2*q+1 by omega)
  have endpoint : p.history.slab k+q*q*p.history.width=p.history.slab (k+1) := by
    dsimp only [GeometryHistory.Plan.slab,GeometryHistory.Plan.stride]
    ring
  rw [endpoint]
  exact bound.trans p.separated

theorem prefix_extend {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) (k : ℕ) (memory : ℕ→Bool) :
    MemoryWord.writeBits (MemoryWord.writeBits memory (p.base+cursor*p.width)
      (prefixBits p initial start level cursor transpose k))
      (p.base+(cursor+count initial start k)*p.width)
      (emittedBits (p.history.layer k) (k+1) (SortArrays.run initial k) (finProdFinEquiv (port initial start k))
        (level+k) (cursor+count initial start k) p.width transpose)=
    MemoryWord.writeBits memory (p.base+cursor*p.width) (prefixBits p initial start level cursor transpose (k+1)) := by
  have address : p.base+(cursor+count initial start k)*p.width=
      p.base+cursor*p.width+(prefixBits p initial start level cursor transpose k).length := by
    rw [prefixBits_length]
    ring
  rw [address,writeBits_append]
  rfl

#print axioms Plan.history_frame
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
