import Maxwell.Continuum.CutoffLoadedGeometry
import Maxwell.Continuum.RationalDataflowTablePrefix

/-! The executed cache retains the actual end of its two allocated buffers.
This is the memory cursor needed to compose later table producers. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost

def Table.EndsBefore {n : ℕ} (a : Table n) (H : ℕ) : Prop :=
  ∀base∈([a.basePositive,a.baseNegative,a.baseDenominator]:List (List Bool)),
    addressValue base+n*addressValue a.width≤H

theorem Table.EndsBefore.mono {n H K : ℕ} {a : Table n}
    (h : a.EndsBefore H) (hHK : H≤K) : a.EndsBefore K :=
  fun base hb => (h base hb).trans hHK

theorem Table.EndsBefore.prefix {n m H : ℕ} {a : Table n}
    (h : a.EndsBefore H) (hm : m≤n) : (a.prefix m hm).EndsBefore H := by
  intro base hb
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ hm) _).trans (h base hb)

theorem Table.EndsBefore.filled {n H : ℕ} {a : Table n}
    (h : a.EndsBefore H) (values : Fin n→Parts) (k : ℕ) : (a.filled values k).EndsBefore H := h

end Maxwell.Continuum.RationalDataflow.PartArray

namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost
set_option maxHeartbeats 2500000

def cacheEndBase (D W heap : ℕ) : ℕ := cacheNextBase D W (cacheNextBase D W heap)

def MonomialCache.EndsBefore {D : ℕ} (a : MonomialCache D) (H : ℕ) : Prop :=
  a.current.EndsBefore H ∧ a.spare.EndsBefore H

theorem MonomialCache.EndsBefore.next {D H : ℕ} {a : MonomialCache D}
    (h : a.EndsBefore H) (j : ℕ) : (a.next j).EndsBefore H := by
  have hm := monomialPassTable_metadata a.current a.spare (a.prepared j) D
  refine ⟨?_,h.1⟩
  simpa only [MonomialCache.next,Table.EndsBefore,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1] using h.2

theorem loadedBuffers_end {n D W : ℕ} (a : Table n) (heap : ℕ)
    (memory memory' : ℕ→Bool) (v : ℕ→Parts) :
    (⟨loadedMonomialTable a (cacheBuffer D W heap memory) 1 0,
      loadedMonomialTable (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0)
        (cacheBuffer D W (cacheNextBase D W heap) memory') 4 7,v⟩ : MonomialCache D).EndsBefore
      (cacheEndBase D W heap) := by
  refine ⟨Table.EndsBefore.mono
    (show (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0).EndsBefore (cacheNextBase D W heap) from
      loadedBuffer_end a heap memory 1 0) ?_,?_⟩
  · unfold cacheEndBase cacheNextBase
    omega
  · exact loadedBuffer_end _ (cacheNextBase D W heap) memory' 4 7

#print axioms MonomialCache.EndsBefore.next
#print axioms loadedBuffers_end
end Maxwell.Continuum.Calibration.RawCutoff
