import Maxwell.Continuum.SourceRoutingCursorLoop
import Mathlib.Data.List.Zip

/-! The actual cursor machine realizes the paper's deterministic completion
of an injective incidence table, in both directions, preserving other arrays. -/

namespace Maxwell.Cost.RoutingPorts.Complete
open Structured Logical.Routing
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

theorem incidenceCompletionPlan_backward {k n : ℕ} (source target : Fin k→Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) :
    let p := incidenceCompletionPlan source target hs ht
    p.backward p.left.length=
      (DummyFill.scatter ((DummyFill.pairs source target).map Prod.swap)).map Fin.val := by
  have hswap : (DummyFill.pairs source target).map Prod.swap=DummyFill.pairs target source := by
    simp only [DummyFill.pairs,List.map_append,List.map_map,List.zip_swap]
    rfl
  have hdata (d : ℕ) :
      (incidenceCompletionPlan source target hs ht).backward d=
        (incidenceCompletionPlan target source ht hs).forward d := by
    simp only [CompletionPlan.backward,CompletionPlan.forward,CompletionPlan.remainingPairs,
      incidenceCompletionPlan,List.map_take,List.zip_swap,realPairs,List.map_map]
    rfl
  dsimp only
  rw [hdata,hswap]
  change (incidenceCompletionPlan target source ht hs).forward
    (DummyFill.unused (DummyFill.incidencePorts source)).length=_
  rw [DummyFill.unused_lengths source target hs ht]
  exact incidenceCompletionPlan_forward target source ht hs

theorem RoutingOutside.preserves {n m : ℕ} {l : Layout n} {s t : BitRAMState}
    (hf : RoutingOutside l s t) (base width : ℕ) (words : Vector (List Bool) m)
    (hs : BitArray.Represents s.memory base width words)
    (hforward : IncidenceEncoding.Separated base (m*width) l.forward (n*n.bits.length))
    (hbackward : IncidenceEncoding.Separated base (m*width) l.backward (n*n.bits.length)) :
    BitArray.Represents t.memory base width words := by
  refine ⟨hs.length,?_⟩
  intro i j hj
  have hi := Nat.mul_le_mul_right width (show i.val+1≤m by omega)
  have outside (target : ℕ) (hh : IncidenceEncoding.Separated base (m*width) target (n*n.bits.length)) :
      base+i.val*width+j<target ∨ target+n*n.bits.length≤base+i.val*width+j := by
    rcases hh with hh|hh
    · left
      nlinarith only [hh,hi,hj]
    · right
      omega
  rw [hf _ (outside _ hforward) (outside _ hbackward)]
  exact hs.bits i j hj

theorem completion_executes {k n : ℕ} (l : Layout n) (source target : Fin k→Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hready : Ready s.val) (hmeta : Metadata l s.val)
    (hstored : Stored l (table (realPairs source target))
      (table ((realPairs source target).map Prod.swap)) s.val)
    (hi : RationalAccumulator.Blank s.val 730) (hj : RationalAccumulator.Blank s.val 731) :
    ∃cost t, Executes input tape cursorCode cost s t ∧ cost≤cursorCost l ∧
      Ready t.val ∧ Metadata l t.val ∧
      Stored l ((DummyFill.scatter (DummyFill.pairs source target)).map Fin.val)
        ((DummyFill.scatter ((DummyFill.pairs source target).map Prod.swap)).map Fin.val) t.val ∧
      CursorFrame l s.val t.val := by
  let p := incidenceCompletionPlan source target hs ht
  have hr : CursorRuntime l p 0 0 0 s := by
    refine ⟨hready,hmeta,?_,(RationalAccumulator.zero_word_iff_blank _ _).mpr hi,
      (RationalAccumulator.zero_word_iff_blank _ _).mpr hj⟩
    exact hstored
  obtain ⟨cost,t,_,he,hc,hout,hframe⟩ := cursor_executes l p input tape s hr
  refine ⟨cost,t,he,hc,hout.ready,hout.metadata,?_,hframe⟩
  have ha := hout.stored
  change Stored l ((incidenceCompletionPlan source target hs ht).forward p.left.length)
    ((incidenceCompletionPlan source target hs ht).backward p.left.length) t.val at ha
  rw [incidenceCompletionPlan_forward,incidenceCompletionPlan_backward] at ha
  exact ha

#print axioms completion_executes
#print axioms RoutingOutside.preserves

end Maxwell.Cost.RoutingPorts.Complete
