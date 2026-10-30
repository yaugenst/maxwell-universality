import Maxwell.Continuum.SourceRoutingControllerWidth
import Maxwell.Continuum.SourceRoutingLevelCoordinates

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ControllerWidth
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def ceiling (heap rootCount rootWidth total : ℕ) : ℕ :=
  heap+stride rootCount rootWidth+rootCount+rootWidth+2^total+4
def baseWidth (heap rootCount rootWidth total : ℕ) : ℕ :=
  (ceiling heap rootCount rootWidth total).bits.length

theorem baseWidth_positive (heap rootCount rootWidth total : ℕ) :
    1 ≤ baseWidth heap rootCount rootWidth total := by
  exact Nat.succ_le_of_lt (RationalAccumulator.bits_nonempty (by dsimp [ceiling];positivity))

theorem population_width (heap rootCount rootWidth total d : ℕ) (hd : d ≤ total) :
    (2^d).bits.length ≤ baseWidth heap rootCount rootWidth total := by
  apply Maxwell.Continuum.RationalWords.bits_mono
  have hh : (2 : ℕ)^d ≤ 2^total := Nat.pow_le_pow_right (by decide) hd
  dsimp only [ceiling]
  omega

theorem reads_width (v : ℕ→ℕ) (heap rootCount rootWidth total d n w j : ℕ)
    (hs : Coordinates.Stored v heap rootCount rootWidth d n w j)
    (hp : v 813=2^d) (hd : d ≤ total) (hn : n ≤ rootCount) (hw : w ≤ rootWidth)
    (hj : j ≤ 2^d) : ∀i∈reads,(v i).bits.length ≤ baseWidth heap rootCount rootWidth total := by
  intro i hi
  apply Maxwell.Continuum.RationalWords.bits_mono
  have power : (2 : ℕ)^d ≤ 2^total := Nat.pow_le_pow_right (by decide) hd
  simp only [reads,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [hs.heap,hs.stride,hs.count,hs.width,hp,hs.first,hs.index,hs.two]
  all_goals dsimp only [ceiling]
  all_goals omega

theorem completed_width (v : ℕ→ℕ) (heap rootCount rootWidth total d n w : ℕ)
    (hs : Coordinates.Stored v heap rootCount rootWidth d n w 0)
    (hp : v 813=2^d) (hd : d ≤ total) (hn : n ≤ rootCount) (hw : w ≤ rootWidth)
    (ht : ∀i∈Division.ids,(v i).bits.length ≤ Level.uniformWidth (baseWidth heap rootCount rootWidth total)) :
    ∀i∈Division.ids,(Level.Advance.output (Level.values v (2^d)) i).bits.length ≤
      Level.uniformWidth (baseWidth heap rootCount rootWidth total) := by
  let L:=baseWidth heap rootCount rootWidth total
  have initial:=reads_width v heap rootCount rootWidth total d n w 0 hs hp hd hn hw (by positivity)
  have word:=population_width heap rootCount rootWidth total d hd
  have completed:=values_width v (2^d) L (Level.uniformWidth L) (baseWidth_positive _ _ _ _)
    initial ht word le_rfl
  have coords:=Level.coordinates_values v heap rootCount rootWidth d n w hs (2^d)
  have nodes : Level.values v (2^d) 813=2^d := (Level.values_other v (2^d) 813 (by decide)).trans hp
  exact advance_width _ L (Level.uniformWidth L)
    (reads_width _ heap rootCount rootWidth total d n w (2^d) coords nodes hd hn hw le_rfl) completed le_rfl

#print axioms completed_width
end Maxwell.Cost.RoutingPorts.Complete.Tree.ControllerWidth
