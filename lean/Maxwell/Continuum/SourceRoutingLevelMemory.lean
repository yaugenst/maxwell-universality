import Maxwell.Continuum.SourceRoutingLevelPlan

/-! A completed prefix of a level writes only its consecutive node blocks. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
set_option maxRecDepth 8192

theorem memory_append {base a b : ℕ} {s t u : ℕ→Bool}
    (hs : Memory.Frame base a s t) (ht : Memory.Frame (base+a) b t u) :
    Memory.Frame base (a+b) s u := by
  intro q hq
  exact (ht q (by omega)).trans (hs q (by omega))

theorem Plan.memory_step {k : ℕ} (p : Plan k) (i : ℕ) (s t u : ℕ→Bool)
    (hs : Memory.Frame (block p.heap p.rootCount p.rootWidth p.first)
      (i*stride p.rootCount p.rootWidth) s t)
    (ht : Memory.Frame (block p.heap p.rootCount p.rootWidth (p.first+i))
      (stride p.rootCount p.rootWidth) t u) :
    Memory.Frame (block p.heap p.rootCount p.rootWidth p.first)
      ((i+1)*stride p.rootCount p.rootWidth) s u := by
  have hh : Memory.Frame (block p.heap p.rootCount p.rootWidth p.first+i*stride p.rootCount p.rootWidth)
      (stride p.rootCount p.rootWidth) t u := by
    simpa only [block,Nat.add_mul,Nat.add_assoc] using ht
  simpa only [Nat.add_mul,Nat.one_mul] using memory_append hs hh

#print axioms Plan.memory_step
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
