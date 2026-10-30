import Maxwell.Continuum.StoredGeometryReadPlan
import Maxwell.Continuum.StoredGeometryRecord
import Maxwell.Continuum.RationalDataflowSizedCounted

/-! The shared invariant of the three chronological geometry passes. The
only geometry premise is the literal fixed-width packed-memory relation. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def fixedIds : Finset ℕ := {960,961,963,964,965,966,967,968,969,970,982,983,984,985}

structure Context {n : ℕ} (values : Vector ℕ n) (base width B : ℕ) (clock : List Bool)
    (constants v : ℕ→ℕ) (s : Store) : Prop where
  ready : Ready v s
  wordWidth : ∀i∈ids,(v i).bits.length≤B
  array : BitArray.Represents s.val.memory base width (IncidenceEncoding.words width values)
  clockWord : BankArray.Word s.val 962 clock
  fixed : ∀i∈fixedIds,v i=constants i

theorem Ready.count_frame {v : ℕ→ℕ} {s t : Store} (h : Ready v s)
    (c : ℕ) (hc : c∈({972,973}:Finset ℕ)) (f : CountedShifted.Frame c s t) : Ready v t := by
  have keep (i : ℕ) (hi : i≠c) : t.val.tapes i=s.val.tapes i := f.2.2.2.2.2.1 i hi
  have c_cases : c=972 ∨ c=973 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hc
  have kz (i : ℕ) (hi : i<10) : t.val.tapes i=s.val.tapes i := keep i (by omega)
  refine ⟨?_,⟨blank_of_eq (kz 0 (by decide)) h.scratch.1,
    blank_of_eq (kz 1 (by decide)) h.scratch.2.1,
    blank_of_eq (kz 2 (by decide)) h.scratch.2.2.1,
    blank_of_eq (kz 3 (by decide)) h.scratch.2.2.2.1,
    blank_of_eq (kz 5 (by decide)) h.scratch.2.2.2.2.1,
    blank_of_eq (kz 6 (by decide)) h.scratch.2.2.2.2.2.1,
    blank_of_eq (kz 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
    blank_of_eq (kz 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩,
    blank_of_eq (kz 7 (by decide)) h.seven⟩
  intro i hi
  apply word_of_eq (keep i ?_) (h.bank i hi)
  simp only [ids,Finset.mem_erase,Finset.mem_Icc] at hi
  omega

theorem Context.count_frame {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s t : Store} (h : Context values base width B clock constants v s)
    (c : ℕ) (hc : c∈({972,973}:Finset ℕ)) (f : CountedShifted.Frame c s t) :
    Context values base width B clock constants v t := by
  refine ⟨h.ready.count_frame c hc f,h.wordWidth,?_,?_,h.fixed⟩
  · simpa only [f.2.2.1] using h.array
  · apply BankArray.word_of_eq (f.2.2.2.2.2.1 962 ?_) h.clockWord
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc
    omega

theorem Context.read_plan {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (h : Context values base width B clock constants v s)
    (targets : List ℕ)
    (ht : ∀t∈targets,t∈ids ∧ t≠960 ∧ t≠961 ∧ t≠962 ∧ t≠971 ∧ t≠970)
    (hf : ∀t∈targets,t∉fixedIds)
    (hw : 0<width) (hB : width≤B) (hlen : clock.length=width) (hn : n.bits.length≤B)
    (hfit : ∀i,(values.get i).bits.length≤width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (hix : v 971+targets.length≤n)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape (readPlanCode targets) cost s t ∧
      cost≤targets.length*(2^22*(B+3)^2)+1 ∧
      Context values base width B clock constants (readPlanValues values targets v) t ∧
      ReadFrame (targets.toFinset∪{971}) s.val t.val := by
  obtain ⟨cost,t,ex,hc,rt,wt,arr,cl,frame⟩ := readPlan_executes values targets ht base width B clock
    hw hB hlen hn hfit v h.wordWidth ((h.fixed 960 (by decide)).trans hb)
    ((h.fixed 961 (by decide)).trans hv) ((h.fixed 970 (by decide)).trans ho)
    hix input tape s h.ready h.clockWord h.array
  refine ⟨cost,t,ex,hc,⟨rt,wt,arr,cl,?_⟩,frame⟩
  intro k hk
  rw [readPlanValues_preserves values targets v k]
  · exact h.fixed k hk
  · intro hh;exact hf k hh hk
  · intro hh;subst k;exact (by decide : (971:ℕ)∉fixedIds) hk

theorem Context.record {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (h : Context values base width B clock constants v s)
    (terminal : Bool) (hc : ∀j,(coordinateValue terminal j v).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape (recordCode terminal) cost s t ∧ cost≤2^28*(B+3)^2 ∧
      Context values base width B clock constants
        (Function.update v 987 (coordinateValue terminal 2 v)) t ∧
      t.val.output=(recordBits terminal v).reverse++s.val.output ∧
      OutputFrame {0,1,2,3,987} s.val t.val := by
  obtain ⟨cost,t,ex,hcst,rt,wt,ot,ft⟩ := record_executes terminal v B h.wordWidth hc input tape s h.ready
  refine ⟨cost,t,ex,hcst,⟨rt,wt,?_,?_,?_⟩,ot,ft⟩
  · simpa only [ft.memory] using h.array
  · exact BankArray.word_of_eq (ft.tapes 962 (by decide)) h.clockWord
  · intro k hk
    rw [Function.update_of_ne (show k≠987 by
      intro hh;subst k;exact (by decide : (987:ℕ)∉fixedIds) hk)]
    exact h.fixed k hk

#print axioms Context.read_plan
#print axioms Context.record
end Maxwell.Continuum.GeometryOutput
