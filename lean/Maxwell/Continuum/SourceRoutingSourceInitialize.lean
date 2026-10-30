import Maxwell.Continuum.SourceRoutingSourceReady
import Maxwell.Logical.CompilerAmplitude

/-! A fixed startup and two actual array fills establish the scatter-loop
invariant directly from the source frontend's represented memory. -/

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Structured SourceGraph.Positive
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def prepareCode : Code := .seq Startup.code Initialize.code
def prepareCost (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  Startup.cost (vertices S p) (base S p)+Initialize.cost (Startup.gridLayout (vertices S p) (base S p))
def prepareWork : Finset ℕ := Startup.allWork∪Initialize.work

theorem initializes (S : Source.SparseSystem) (p : ℕ) (hm : 2≤S.nnz)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : SourceGraph.Incidence.Result S p s) :
    ∃steps t clock, Executes input tape prepareCode steps s t ∧ steps≤prepareCost S p ∧
      Scatter.Runtime (plan S p clock hs.room) 0 t ∧ Word t.val 142 (4*count S p) ∧
      Blank t.val 779 ∧ RoutingOutside (plan S p clock hs.room).routing s.val t.val ∧
      ArchiveFrame prepareWork s.val t.val := by
  have hd : 2≤dimension S p := Logical.sourceCircuit_size_two_le S hm p
  have hv : 0<vertices S p := by unfold vertices; omega
  obtain ⟨clock,hdesc⟩ := descriptor hs
  let pp := plan S p clock hs.room
  obtain ⟨ca,a,ea,hca,ra,ma,_a705,_a706,a710,_a719,_a708,_a712,fa⟩ :=
    Startup.executes (vertices S p) (base S p) hv input tape s
      hs.numeric.vertices hs.numeric.diagonalBase (ready hs) (startup_fresh hs)
  have fresh (i : ℕ) (hlo : 163 ≤ i) (h500 : i < 500 ∨ 509 < i) (h600 : i < 600 ∨ 612 < i) :
      Blank s.val i := ⟨0,hs.fresh i hlo h500 h600⟩
  have freshA (i : ℕ) (hi : i=730 ∨ i=732 ∨ i=739) : Blank a.val i := by
    apply RationalAccumulator.blank_of_eq (fa.tapes i ?_)
      (fresh i (by omega) (Or.inr (by omega)) (Or.inr (by omega)))
    simp only [Startup.allWork,Startup.banks,Size.banks,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.mem_Icc]
    omega
  obtain ⟨cb,t,eb,hcb,rt,mt,t730,_t732,_t739,stored,outside,fb⟩ :=
    Initialize.initializes_both pp.routing input tape a ra ma
      (freshA 730 (by decide)) (freshA 732 (by decide)) (freshA 739 (by decide))
  have frame : ArchiveFrame prepareWork s.val t.val :=
    ((ArchiveFrame.of_binary fa).mono Finset.subset_union_left).trans
      ((ArchiveFrame.of_complete fb).mono Finset.subset_union_right)
  have outside' : RoutingOutside pp.routing s.val t.val :=
    (RoutingOutside.of_memory fa.memory).trans outside
  have dt : Scatter.Descriptor pp.inputLayout clock t.val := hdesc.transport (by
    intro i hi
    apply frame.tapes i
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have bank : NatAssign.Bank PortArithmetic.ids (Scatter.seed pp.half 0 0 0) t.val := by
    intro i hi
    by_cases h710 : i=710
    · subst i
      exact RationalAccumulator.word_of_eq (fb.tapes 710 (by decide) (by decide)) a710
    · have hz : Blank t.val i := by
        by_cases h730 : i=730
        · subst i
          exact t730
        · have hrange : 220 ≤ i ∧ (i≤223 ∨ 730 ≤ i) ∧ i≤768 := by
            simp only [PortArithmetic.ids,PortArithmetic.ports,
              Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_union,
              Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
            omega
          apply RationalAccumulator.blank_of_eq (frame.tapes i (Or.inr (by omega)) ?_)
            (fresh i (by omega) (by omega) (by omega))
          simp only [PortArithmetic.ids,PortArithmetic.ports,
            Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_union,
            Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
          simp only [prepareWork,Startup.allWork,Startup.banks,Size.banks,Initialize.work,
            Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
          omega
      simpa [Scatter.seed,h710] using (RationalAccumulator.zero_word_iff_blank _ _).mpr hz
  refine ⟨ca+cb,t,clock,ea.seq eb,Nat.add_le_add hca hcb,
    ⟨Nat.zero_le _,rt,mt,dt,?_,?_,?_,bank,?_⟩,?_,?_,outside',frame⟩
  · exact outside'.preserves _ _ _ hs.incidence.endpoints pp.endpoint_forward pp.endpoint_backward
  · exact outside'.preserves _ _ _ hs.incidence.ranks pp.rank_forward pp.rank_backward
  · simpa only [Scatter.forward_zero,Scatter.backward] using stored
  · exact RationalAccumulator.blank_of_eq (frame.tapes 753 (by decide) (by decide))
      (fresh 753 (by decide) (by decide) (by decide))
  · exact RationalAccumulator.word_of_eq (frame.tapes 142 (by decide) (by decide)) hs.numeric.incidences
  · exact RationalAccumulator.blank_of_eq (frame.tapes 779 (by decide) (by decide))
      (fresh 779 (by decide) (by decide) (by decide))

#print axioms initializes

end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
