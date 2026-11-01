import Maxwell.Continuum.SourceRoutingPathStep
import Maxwell.Logical.Routing.SortPaths

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
open Maxwell.Logical.Routing GeometryPath
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

export Maxwell.Logical.Routing.SortPaths (port length count length_bound count_bound)

structure Plan (q : ℕ) where
  history : GeometryHistory.Plan q
  base : ℕ
  width : ℕ
  clock : List Bool
  positive : 0<width
  clock_length : clock.length=width
  coordinate_width : (1024*q+1).bits.length ≤ width
  separated : history.slab (2*q+1) ≤ base

def Plan.bound {q : ℕ} (p : Plan q) (n : ℕ) : ℕ :=
  p.history.bound+(6*q+1).bits.length+2*n.bits.length+p.width+p.base.bits.length+64

def prefixBits {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) : ℕ→List Bool
  | 0 => []
  | k+1 => prefixBits p initial start level cursor transpose k++
      emittedBits (p.history.layer k) (k+1) (SortArrays.run initial k) (finProdFinEquiv (port initial start k))
        (level+k) (cursor+count initial start k) p.width transpose

theorem prefixBits_length {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor : ℕ) (transpose : Bool) (k : ℕ) :
    (prefixBits p initial start level cursor transpose k).length=count initial start k*p.width := by
  induction k with
  | zero => simp [prefixBits,count]
  | succ k ih =>
    rw [prefixBits,List.length_append,ih,emittedBits_length,Equiv.symm_apply_apply]
    change count initial start k*p.width+3*length initial start k*p.width=
      (count initial start k+3*length initial start k)*p.width
    ring

theorem Plan.emit_bound {q : ℕ} (p : Plan q) (k level cursor n : ℕ)
    (layer : k ≤ 2*q) (height : level ≤ 6*q) (room : cursor ≤ n) :
    emitBound (p.history.layer k) (k+1) level cursor p.width p.base n ≤ p.bound n := by
  have hp:=p.history.layer_bound k layer
  have hl:=Maxwell.Continuum.RationalWords.bits_mono (show level ≤ 6*q+1 by omega)
  have hc:=Maxwell.Continuum.RationalWords.bits_mono room
  dsimp only [emitBound,prepareBound,Plan.bound]
  omega

#print axioms prefixBits_length
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
