import Maxwell.Continuum.SourceRoutingAssemblyAdvanceWidth
import Maxwell.Continuum.SourceRoutingAssemblyLevelCompleted
import Maxwell.Continuum.SourceRoutingTraversalWidth

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def baseWidth (heap rootCount rootWidth total : ℕ) : ℕ :=
  ControllerWidth.baseWidth heap rootCount rootWidth total+2

theorem reads_width (v : ℕ→ℕ) (heap rootCount rootWidth total d k j : ℕ)
    (hs : AssemblyCoordinates.Stored v heap rootCount rootWidth d k j)
    (hp : v 813=2^d) (hd : d ≤ total) (hn : 2^k ≤ rootCount) (hw : k+1 ≤ rootWidth)
    (hj : j ≤ 2^d) : ∀i∈ControllerWidth.reads,(v i).bits.length ≤
      baseWidth heap rootCount rootWidth total := by
  intro i hi
  apply Nat.le_trans (m:=ControllerWidth.baseWidth heap rootCount rootWidth total) ?_ (by
    dsimp only [baseWidth];omega)
  apply Maxwell.Continuum.RationalWords.bits_mono
  have power : (2 : ℕ)^d ≤ 2^total := Nat.pow_le_pow_right (by decide) hd
  simp only [ControllerWidth.reads,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [hs.heap,hs.stride,hs.count,hs.width,hp,hs.first,hs.index,hs.two]
  all_goals dsimp only [ControllerWidth.ceiling]
  all_goals omega

theorem completed_width (v : ℕ→ℕ) (heap rootCount rootWidth total d k : ℕ)
    (hs : AssemblyCoordinates.Stored v heap rootCount rootWidth d k 0)
    (hp : v 813=2^d) (hd : d ≤ total) (hn : 2^k ≤ rootCount) (hw : k+1 ≤ rootWidth)
    (ht : ∀i∈Division.ids,(v i).bits.length ≤
      AssemblyLevel.uniformWidth (baseWidth heap rootCount rootWidth total)) :
    ∀i∈Division.ids,(AssemblyLevel.nextValues v (2^d) i).bits.length ≤
      AssemblyLevel.uniformWidth (baseWidth heap rootCount rootWidth total) := by
  let L:=baseWidth heap rootCount rootWidth total
  have hL : 2 ≤ L := by dsimp only [L,baseWidth];omega
  have initial:=reads_width v heap rootCount rootWidth total d k 0 hs hp hd hn hw (by positivity)
  have word : (2^d).bits.length ≤ L :=
    (ControllerWidth.population_width heap rootCount rootWidth total d hd).trans (by dsimp only [L,baseWidth];omega)
  have completed:=AssemblyLevel.values_width v (2^d) L (AssemblyLevel.uniformWidth L)
    hL initial ht word le_rfl
  have coords:=AssemblyLevel.coordinates v heap rootCount rootWidth d k hs (2^d)
  have nodes : AssemblyLevel.values v (2^d) 813=2^d :=
    (AssemblyLevel.values_other v (2^d) 813 (by decide)).trans hp
  exact AssemblyAdvance.words _ L (AssemblyLevel.uniformWidth L) (by omega)
    (reads_width _ heap rootCount rootWidth total d k (2^d) coords nodes hd hn hw le_rfl) completed le_rfl

#print axioms completed_width
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
