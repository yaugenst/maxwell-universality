import Maxwell.Continuum.WellInternalEntry
import Maxwell.Continuum.StoredGeometryTerminal
import Maxwell.Cost.PhysicalEmit.Increment
import Maxwell.Cost.Structured.Footprint

/-! Each internal sample is consumed from the packed geometry before its
constant degree-two strength is written at the next chronological index. -/
namespace Maxwell.Continuum.RationalDataflow.WellInternalGeometry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open WellStrengthPass
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def code : Code := .seq (GeometryOutput.readPlanCode (GeometryOutput.tripleTargets false))
  (.seq WellInternalEntry.code (PhysicalEmit.incrementCode 999))

def costBound (P B M : ℕ) : ℕ :=
  3*(2^22*(B+3)^2)+1+WellInternalEntry.costBound P B M+12*M+18

theorem executes {n J base width B P M boundary : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store} (g : GeometryOutput.Context data base width B clock constants gv s)
    (hw : 0<width) (hB : width ≤ B) (hlen : clock.length=width) (hn : n.bits.length ≤ B)
    (hfit : ∀i,(data.get i).bits.length ≤ width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (cursor : ℕ) (hcursor : gv 971=cursor) (hspan : cursor+3 ≤ n)
    (v : ℕ→Parts) (canonical : WellStrengthReset.canonical v=v)
    (hW : 4 ≤ B) (hP : (2^P).bits.length ≤ B) (rvwidth : WidthBank WellStrength.bank B v)
    (good : Good WellStrength.bank v) (scale : (v 4).value ≠ 0)
    (denominator : (v 1).value+WellTarget.target .internal v ≠ 0)
    (a : PartArray.Table J) (i : Fin J) (hindex : i.val.bits.length ≤ M)
    (config : Configuration a P B M boundary) (harray : base+n*width ≤ boundary)
    (state : State a P v i.val s) (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t gv',Executes input tape code cost s t ∧ cost ≤ costBound P B M ∧
      GeometryOutput.Context data base width B clock constants gv' t ∧ gv' 971=cursor+3 ∧
      State (a.set i (WellInternalEntry.part P v)) P v (i.val+1) t ∧
      t.val.memory=a.writeMemory i (WellInternalEntry.part P v) s.val.memory ∧
      (WellInternalEntry.part P v).Width (addressValue a.width) ∧
      (∀k,k∈({972,973,988}:Finset ℕ)→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,e0,hc0,g0,f0⟩ := g.read_plan (GeometryOutput.tripleTargets false)
    (GeometryOutput.tripleTargets_valid false) (GeometryOutput.tripleTargets_fixed false)
    hw hB hlen hn hfit hb hv ho (by rw [GeometryOutput.tripleTargets_length,hcursor];exact hspan) input tape
  have state0 := state.geometry_frame g0.ready f0.memory (e0.protectsTape 4 (by decide))
    (fun k hk kout _=>f0.tapes k hk (by
      change k∉({976,977,978,971}:Finset ℕ)
      simp only [Finset.mem_insert,Finset.mem_singleton];omega))
    (word_of_eq (f0.tapes 999 (by decide) (by decide)) state.outputIndex)
  obtain ⟨c1,w,e1,hc1,state1,memory1,width1,keep1⟩ := WellInternalEntry.executes a i config hindex
    v canonical hW hP rvwidth good scale denominator input tape u state0
  have g1 := geometry_after_write g0 i (WellInternalEntry.part P v) state1.table memory1
    (fun b hb=>harray.trans (config.above b hb)) keep1
  obtain ⟨c2,t,hc2,e2,index2,f2⟩ := PhysicalEmit.increment 999 i.val input tape w state1.outputIndex
  have frame2 : BinaryPrecision.Frame {999} w.val t.val :=
    ⟨f2.address,f2.inputHead,f2.memory,f2.randomCursor,f2.output,f2.tapes⟩
  have g2 := geometry_index_frame g1 frame2
  have state2 := state1.geometry_frame g2.ready f2.memory (f2.tapes 4 (by decide))
    (fun k _ _ hk=>f2.tapes k (by simpa only [Finset.mem_singleton] using hk)) index2
  refine ⟨c0+(c1+c2),t,_,e0.seq (e1.seq e2),?_,g2,?_,state2,?_,width1,?_⟩
  · rw [GeometryOutput.tripleTargets_length] at hc0
    unfold costBound
    omega
  · rw [GeometryOutput.readPlanValues_cursor,GeometryOutput.tripleTargets_length,hcursor]
  · rw [f2.memory,memory1,f0.memory]
  · intro k hk
    have cases : k=972 ∨ k=973 ∨ k=988 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hk
    exact (f2.tapes k (by simp only [Finset.mem_singleton];omega)).trans
      ((keep1 k (by omega) (by omega)).trans (f0.tapes k (by omega) (by
        rcases cases with rfl|rfl|rfl <;> decide)))

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellInternalGeometry
