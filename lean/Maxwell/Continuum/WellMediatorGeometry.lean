import Maxwell.Continuum.WellStrengthPassState
import Maxwell.Continuum.StoredGeometryMediator
import Maxwell.Cost.PhysicalEmit.Increment
import Maxwell.Cost.Structured.Footprint

/-! A concrete mediator body reads the next saved point, computes its
strength from the actual adjacent pair, and advances the point and table
cursors. Its value is indexed solely by the chronological packed array. -/
namespace Maxwell.Continuum.RationalDataflow.WellMediatorGeometry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open WellStrengthPass
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def coupling {n : ℕ} (data : Vector ℕ n) (cursor : ℕ) (v : ℕ→Parts) : ℚ :=
  if GeometryOutput.arrayValue data cursor ≠ GeometryOutput.arrayValue data (cursor+3) then (v 5).value else
    if GeometryOutput.arrayValue data (cursor+1) ≠ GeometryOutput.arrayValue data (cursor+4) then (v 6).value
      else (v 7).value

def target {n : ℕ} (data : Vector ℕ n) (cursor : ℕ) (v : ℕ→Parts) : ℚ :=
  -(coupling data cursor v)^2/(v 4).value

def part {n : ℕ} (P : ℕ) (data : Vector ℕ n) (cursor : ℕ) (v : ℕ→Parts) : Parts :=
  Parts.literal (WellStrength.numerator P (v 1).value (target data cursor v):ℚ)

theorem read_target {n : ℕ} (data : Vector ℕ n) (cursor : ℕ) (v : ℕ→Parts) (gv : ℕ→ℕ)
    (hi : gv 971=cursor+3)
    (hp : ∀j:Fin 3,gv (976+j.val)=GeometryOutput.arrayValue data (cursor+j.val)) :
    WellMediatorEntry.target (GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets true) gv) v=
      target data cursor v := by
  let w := GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets true) gv
  have prev (j : Fin 3) : w (976+j.val)=GeometryOutput.arrayValue data (cursor+j.val) := by
    rw [show w (976+j.val)=gv (976+j.val) from GeometryOutput.readPlanValues_preserves data _ _ _
      (by fin_cases j <;> decide) (by omega)]
    exact hp j
  have next (j : Fin 3) : w (979+j.val)=GeometryOutput.arrayValue data (cursor+3+j.val) := by
    simpa only [ite_true,hi] using GeometryOutput.tripleValues_get data true gv j
  change -(WellMediatorLoad.coupling w v)^2/(v 4).value=_
  have p0 := prev 0
  have p1 := prev 1
  have n0 := next 0
  have n1 := next 1
  dsimp at p0 p1 n0 n1
  simp only [WellMediatorLoad.coupling,p0,p1,n0,n1,target,coupling]

def code : Code := .seq (GeometryOutput.readPlanCode (GeometryOutput.tripleTargets true))
  (.seq WellMediatorEntry.code (.seq (NatAssign.code GeometryOutput.copyNextPlan) (PhysicalEmit.incrementCode 999)))

def costBound (P B M : ℕ) : ℕ := 3*(2^22*(B+3)^2)+1+WellMediatorEntry.costBound P B M+
  2^23*(B+3)^2+12*M+18

theorem executes {n J base width B P M : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store} (g : GeometryOutput.Context data base width B clock constants gv s)
    (hw : 0<width) (hB : width ≤ B) (hlen : clock.length=width) (hn : n.bits.length ≤ B)
    (hfit : ∀i,(data.get i).bits.length ≤ width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (cursor : ℕ) (hcursor : gv 971=cursor+3) (hspan : cursor+6 ≤ n)
    (hprev : ∀j:Fin 3,gv (976+j.val)=GeometryOutput.arrayValue data (cursor+j.val))
    (v : ℕ→Parts) (canonical : WellStrengthReset.canonical v=v)
    (hW : 4 ≤ B) (hP : (2^P).bits.length ≤ B) (rvwidth : WidthBank WellStrength.bank B v)
    (good : Good WellStrength.bank v) (scale : (v 4).value ≠ 0)
    (denominator : (v 1).value+target data cursor v ≠ 0)
    (a : PartArray.Table J) (i : Fin J) (hindex : i.val.bits.length ≤ M)
    (hmeta : a.MetadataWidth M) (hpart : P+4096*(256*(B+1))+4179 ≤ addressValue a.width)
    (hsep : a.Separated)
    (below : ∀b∈[a.basePositive,a.baseNegative,a.baseDenominator],base+n*width ≤ addressValue b)
    (state : State a P v i.val s) (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t gv',Executes input tape code cost s t ∧ cost ≤ costBound P B M ∧
      GeometryOutput.Context data base width B clock constants gv' t ∧ gv' 971=cursor+6 ∧
      (∀j:Fin 3,gv' (976+j.val)=GeometryOutput.arrayValue data (cursor+3+j.val)) ∧
      State (a.set i (part P data cursor v)) P v (i.val+1) t ∧
      t.val.memory=a.writeMemory i (part P data cursor v) s.val.memory ∧
      (part P data cursor v).Width (addressValue a.width) ∧
      (∀k,k∈({972,973,988}:Finset ℕ)→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,e0,hc0,g0,f0⟩ := g.read_plan (GeometryOutput.tripleTargets true)
    (GeometryOutput.tripleTargets_valid true) (GeometryOutput.tripleTargets_fixed true)
    hw hB hlen hn hfit hb hv ho (by rw [GeometryOutput.tripleTargets_length,hcursor];omega) input tape
  have state0 := state.geometry_frame g0.ready f0.memory (e0.protectsTape 4 (by decide))
    (fun k hk kout _=>f0.tapes k hk (by
      change k∉({979,980,981,971}:Finset ℕ)
      simp only [Finset.mem_insert,Finset.mem_singleton];omega))
    (word_of_eq (f0.tapes 999 (by decide) (by decide)) state.outputIndex)
  have selected := read_target data cursor v gv hcursor hprev
  have gw : ∀x∈WellMediatorLoad.plan,
      (GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets true) gv x.1).bits.length ≤ B := by
    intro x hx
    apply g0.wordWidth
    simp only [WellMediatorLoad.plan,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> decide
  have words : ∀x∈WellMediatorLoad.plan,Word u.val x.1
      (GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets true) gv x.1) := by
    intro x hx
    apply g0.ready.bank
    simp only [WellMediatorLoad.plan,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> decide
  obtain ⟨c1,w,e1,hc1,r1,out1,memory1,width1,clean1,power1,index1,keep1⟩ := WellMediatorEntry.executes
    a P B M hW hP _ v canonical rvwidth good scale (by rwa [selected]) gw i i.val.bits
    (addressValue_bits i.val) hindex hmeta hpart hsep input tape u state0.rational state0.clean state0.power
    state0.table state0.outputIndex words
  have partEq : WellMediatorEntry.part P (GeometryOutput.readPlanValues data (GeometryOutput.tripleTargets true) gv) v=
      part P data cursor v := by simp only [WellMediatorEntry.part,part,selected]
  rw [partEq] at out1 memory1 width1
  have state1 : State (a.set i (part P data cursor v)) P v i.val w := ⟨r1,clean1,power1,out1,index1⟩
  have g1 := geometry_after_write g0 i (part P data cursor v) out1 memory1 below keep1
  obtain ⟨c2,z,e2,hc2,g2,f2⟩ := GeometryOutput.copyNext_executes g1 input tape
  have state2 := state1.geometry_frame g2.ready f2.memory (f2.tapes 4 (by decide))
    (fun k hk kout _=>f2.tapes k (by simp only [Finset.mem_insert,Finset.mem_singleton];omega))
    (word_of_eq (f2.tapes 999 (by decide)) state1.outputIndex)
  obtain ⟨c3,t,hc3,e3,index3,f3⟩ := PhysicalEmit.increment 999 i.val input tape z state2.outputIndex
  have frame3 : BinaryPrecision.Frame {999} z.val t.val :=
    ⟨f3.address,f3.inputHead,f3.memory,f3.randomCursor,f3.output,f3.tapes⟩
  have g3 := geometry_index_frame g2 frame3
  have state3 := state2.geometry_frame g3.ready f3.memory (f3.tapes 4 (by decide))
    (fun k _ _ hk=>f3.tapes k (by simpa only [Finset.mem_singleton] using hk)) index3
  refine ⟨c0+(c1+(c2+c3)),t,_,e0.seq (e1.seq (e2.seq e3)),?_,g3,?_,?_,state3,?_,width1,?_⟩
  · rw [GeometryOutput.tripleTargets_length] at hc0
    unfold costBound
    omega
  · rw [GeometryOutput.copyNext_preserves _ 971 (by decide),GeometryOutput.readPlanValues_cursor,
      GeometryOutput.tripleTargets_length,hcursor]
  · intro j
    rw [GeometryOutput.copyNext_get]
    simpa only [ite_true,hcursor] using GeometryOutput.tripleValues_get data true gv j
  · rw [f3.memory,f2.memory,memory1,f0.memory]
  · intro k hk
    have cases : k=972 ∨ k=973 ∨ k=988 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hk
    exact (f3.tapes k (by simp only [Finset.mem_singleton];omega)).trans
      ((f2.tapes k (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)).trans
        ((keep1 k (by omega) (by omega)).trans (f0.tapes k (by omega) (by
          rcases cases with rfl|rfl|rfl <;> decide))))

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellMediatorGeometry
