import Maxwell.Continuum.CutoffCacheGeometry
import Maxwell.Continuum.CutoffMonomialInitialize

/-! Allocation changes only the output descriptor and natural scratch.
The live rational register bank and input coefficient table are retained. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem cacheAllocation_rational_frame {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready (Finset.range 8) v s)
    (f : BinaryPrecision.Frame Profile.Runtime.CacheAllocation.changed s.val t.val)
    (hz : NatAssign.Scratch t.val) : RationalDataflow.Ready (Finset.range 8) v t := by
  refine ⟨?_,hz⟩
  have hd : Disjoint (ids (Finset.range 8)) Profile.Runtime.CacheAllocation.changed := by decide
  intro i hi
  exact RationalAccumulator.word_of_eq (f.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh)) (h.1 i hi)

theorem cacheTable_disjoint_after {n : ℕ} (a : Table n) (D W heap : ℕ) (memory : ℕ→Bool)
    (ha : ∀base∈([a.basePositive,a.baseNegative,a.baseDenominator]:List (List Bool)),
      addressValue base+n*addressValue a.width≤heap) :
    a.SeparatedFrom (Profile.Runtime.memoryTable (4*(D+1)) (monomialWorkingWidth D W) heap
      (cache_working_pos D W) memory) := by
  intro base hb out ho
  simp only [Profile.Runtime.memoryTable,List.mem_cons,List.not_mem_nil,or_false] at ho
  have h := ha base hb
  rcases ho with rfl|rfl|rfl <;>
    simp only [Profile.Runtime.memoryTable,addressValue_bits,IncidenceEncoding.Separated] <;>
    left <;> omega

theorem initialize_preserves_auxiliary (second : Bool) :
    ([206,207,208,209,709,721,722,723,724,726,727,728,729]:List ℕ).all
      (fun i => (monomialInitializeCode second).protectsTape i)=true := by
  cases second <;> decide

theorem initialize_keeps_auxiliary {input : List Bool} {tape : ℕ→Bool} {cost : ℕ}
    {s t : Store} {second : Bool} (e : Executes input tape (monomialInitializeCode second) cost s t)
    (i : ℕ) (hi : i∈([206,207,208,209,709,721,722,723,724,726,727,728,729]:List ℕ)) :
    t.val.tapes i=s.val.tapes i :=
  e.protectsTape i (List.all_eq_true.mp (initialize_preserves_auxiliary second) i hi)

#print axioms cacheAllocation_rational_frame
#print axioms cacheTable_disjoint_after
#print axioms initialize_preserves_auxiliary
end Maxwell.Continuum.Calibration.RawCutoff
