import Maxwell.Continuum.SourceRoutingSortGenerate

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Plan (q : ℕ) where
  base : ℕ
  clock : List Bool
  positive : 0<q
  clock_length : clock.length=(q*q).bits.length

def Plan.width {q : ℕ} (_p : Plan q) : ℕ := (q*q).bits.length
def Plan.stride {q : ℕ} (p : Plan q) : ℕ := q*q*p.width
def Plan.slab {q : ℕ} (p : Plan q) (k : ℕ) : ℕ := p.base+k*p.stride
def Plan.layer {q : ℕ} (p : Plan q) (k : ℕ) : GeometrySort.Plan q where
  source := p.slab k
  destination := p.slab (k+1)
  clock := p.clock
  positive := p.positive
  clock_length := p.clock_length
  separated := Or.inl (le_of_eq (by dsimp only [Plan.slab,Plan.stride,Plan.width];ring))

def Plan.bound {q : ℕ} (p : Plan q) : ℕ :=
  p.width+q.bits.length+(2*q+1).bits.length+2*(p.slab (2*q+1)).bits.length+32

theorem Plan.slab_mono {q : ℕ} (p : Plan q) {a b : ℕ} (h : a ≤ b) : p.slab a ≤ p.slab b :=
  Nat.add_le_add_left (Nat.mul_le_mul_right p.stride h) p.base

theorem Plan.layer_bound {q : ℕ} (p : Plan q) (k : ℕ) (hk : k ≤ 2*q) :
    (p.layer k).bound (k+1) ≤ p.bound := by
  have hround:=Maxwell.Continuum.RationalWords.bits_mono (show k+1 ≤ 2*q+1 by omega)
  have hsource:=Maxwell.Continuum.RationalWords.bits_mono (p.slab_mono (show k ≤ 2*q+1 by omega))
  have hdest:=Maxwell.Continuum.RationalWords.bits_mono (p.slab_mono (show k+1 ≤ 2*q+1 by omega))
  dsimp only [GeometrySort.Plan.bound,GeometrySort.Plan.width,Plan.layer,Plan.bound,Plan.width]
  omega

theorem step_parity {q : ℕ} (round : ℕ) (saved : SortArrays.Keys q) :
    SortArrays.step round saved=SortArrays.step (round%2) saved := by
  simp only [SortArrays.step,SortArrays.center,decide_eq_true_eq,Nat.mod_mod]

theorem run_succ {q : ℕ} (initial : SortArrays.Keys q) (k : ℕ) :
    SortArrays.run initial (k+1)=SortArrays.step (k+1) (SortArrays.run initial k) := by
  rw [step_parity]
  rfl

theorem run_fits {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q)
    (fit : GeometrySort.Fits p.width initial) (k : ℕ) :
    GeometrySort.Fits p.width (SortArrays.run initial k) := by
  induction k with
  | zero => exact fit
  | succ k ih => exact GeometrySort.step_fits _ _ _ ih

def Stored {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (k : ℕ) (memory : ℕ→Bool) : Prop :=
  ∀j,j ≤ k→BitArray.Represents memory (p.slab j) p.width
    (IncidenceEncoding.words p.width (SortArrays.run initial j))

theorem Stored.next {q k : ℕ} {p : Plan q} {initial : SortArrays.Keys q} {before after : ℕ→Bool}
    (stored : Stored p initial k before)
    (next : BitArray.Represents after (p.slab (k+1)) p.width
      (IncidenceEncoding.words p.width (SortArrays.run initial (k+1))))
    (frame : Tree.Memory.Frame (p.slab (k+1)) p.stride before after) :
    Stored p initial (k+1) after := by
  intro j hj
  by_cases same : j=k+1
  · simpa only [same] using next
  · apply frame.represents (Or.inl ?_) (stored j (by omega))
    change p.slab j+p.stride ≤ p.slab (k+1)
    calc
      _ = p.slab (j+1) := by dsimp only [Plan.slab];ring
      _ ≤ _ := p.slab_mono (by omega)

def MemoryFrame {q : ℕ} (p : Plan q) := Tree.Memory.Frame (p.slab 1) (2*q*p.stride)

theorem layer_frame {q k : ℕ} (p : Plan q) (hk : k<2*q) {before after : ℕ→Bool}
    (frame : Tree.Memory.Frame (p.slab (k+1)) p.stride before after) : MemoryFrame p before after := by
  intro address outside
  apply frame address
  have lower:=p.slab_mono (show 1 ≤ k+1 by omega)
  have upper:=p.slab_mono (show k+2 ≤ 2*q+1 by omega)
  have endpoint : p.slab (k+1)+p.stride=p.slab (k+2) := by dsimp only [Plan.slab];ring
  have total : p.slab 1+2*q*p.stride=p.slab (2*q+1) := by dsimp only [Plan.slab];ring
  rcases outside with outside|outside
  · exact Or.inl (outside.trans_le lower)
  · exact Or.inr (by omega)

#print axioms Stored.next
#print axioms run_fits
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
