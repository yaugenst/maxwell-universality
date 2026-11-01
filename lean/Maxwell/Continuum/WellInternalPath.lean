import Maxwell.Continuum.WellInternalLoop
import Maxwell.Continuum.StoredGeometryPathSetup
import Maxwell.Cost.Structured.CounterClear

/-! An internal path reads its length header, skips both original endpoints,
computes each internal strength, and clears its padded counter. -/
namespace Maxwell.Continuum.RationalDataflow.WellInternalGeometry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open WellStrengthPass
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def pathCode : Code := .seq (GeometryOutput.pathSetupCode 2) (.seq loopCode
  (.seq (GeometryOutput.readPlanCode (GeometryOutput.tripleTargets false)) (.call (TapeOps.clear 973))))

def pathCost (P B M count : ℕ) : ℕ :=
  2^27*(B+3)^2+(count+1)*(13*B+15)+count*costBound P B M+6*B+4

theorem path_executes {n J base width B P M boundary : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store} (g : GeometryOutput.Context data base width B clock constants gv s)
    (hw : 0<width) (hB : width ≤ B) (hlen : clock.length=width) (hn : n.bits.length ≤ B)
    (hfit : ∀i,(data.get i).bits.length ≤ width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (start count first : ℕ) (hcursor : gv 971=start) (hspan : start+1+3*count ≤ n)
    (hcount : GeometryOutput.arrayValue data start=count) (htwo : 2 ≤ count)
    (v : ℕ→Parts) (canonical : WellStrengthReset.canonical v=v)
    (hW : 4 ≤ B) (hP : (2^P).bits.length ≤ B) (rvwidth : WidthBank WellStrength.bank B v)
    (good : Good WellStrength.bank v) (scale : (v 4).value ≠ 0)
    (denominator : (v 1).value+WellTarget.target .internal v ≠ 0)
    (a : PartArray.Table J) (config : Configuration a P B M boundary)
    (harray : base+n*width ≤ boundary) (hcapacity : first+(count-2) ≤ J) (hJ : J.bits.length ≤ M)
    (values : ℕ→Parts) (completed : a.CorrectPrefix values first)
    (agrees : ∀j<count-2,values (first+j)=WellInternalEntry.part P v)
    (memory : ℕ→Bool) (saved : ∀k,k<boundary→s.val.memory k=memory k)
    (state : State a P v first s) (input : List Bool) (tape : ℕ→Bool)
    (old : List Bool) (hold : BankArray.Word s.val 973 old) (oldWidth : old.length ≤ B) :
    ∃cost t,∃a':PartArray.Table J,∃gv',Executes input tape pathCode cost s t ∧
      cost ≤ pathCost P B M count ∧ GeometryOutput.Context data base width B clock constants gv' t ∧
      gv' 971=start+1+3*count ∧ State a' P v (first+(count-2)) t ∧ Configuration a' P B M boundary ∧
      a'.CorrectPrefix values (first+(count-2)) ∧ (∀k,k<boundary→t.val.memory k=memory k) ∧
      Blank t.val 973 ∧ (∀k,k∈({972,988}:Finset ℕ)→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,word,origin,w,e0,hc0,g0,ix,_,word0,len,val0,_,keep0⟩ :=
    GeometryOutput.pathSetup_executes g hw hB hlen hn hfit hb hv ho start count 2 hcursor
      (by omega) hcount (by omega) (by decide) old hold oldWidth input tape
  have memory0 : u.val.memory=s.val.memory := e0.protectsMemory (by decide)
  have state0 := state.geometry_frame g0.ready memory0 (e0.protectsTape 4 (by decide))
    (fun k hk kout _=>keep0 k hk (by simp only [Finset.mem_insert,Finset.mem_singleton];omega))
    (word_of_eq (keep0 999 (by decide) (by decide)) state.outputIndex)
  obtain ⟨c1,z,b,w',lastWord,e1,hc1,g1,ix1,state1,cf1,done1,mem1,word1,len1,keep1⟩ :=
    loop_executes g0 hw hB hlen hn hfit hb hv ho (start+4) (count-2) first ix (by omega)
      v canonical hW hP rvwidth good scale denominator a config harray hcapacity hJ values completed agrees
      memory (by intro k hk;rw [memory0];exact saved k hk) state0 input tape word origin val0 word0
  obtain ⟨c2,u2,e2,hc2,g2,f2⟩ := g1.read_plan (GeometryOutput.tripleTargets false)
    (GeometryOutput.tripleTargets_valid false) (GeometryOutput.tripleTargets_fixed false)
    hw hB hlen hn hfit hb hv ho (by rw [GeometryOutput.tripleTargets_length,ix1];omega) input tape
  have state2 := state1.geometry_frame g2.ready f2.memory (e2.protectsTape 4 (by decide))
    (fun k hk kout _=>f2.tapes k hk (by
      change k∉({976,977,978,971}:Finset ℕ)
      simp only [Finset.mem_insert,Finset.mem_singleton];omega))
    (word_of_eq (f2.tapes 999 (by decide) (by decide)) state1.outputIndex)
  obtain ⟨t,e3,blank3,frame3⟩ := RuntimeCounter.clear_executes 973 input tape lastWord origin u2
    ((f2.tapes 973 (by decide) (by decide)).trans word1)
  have g3 := geometry_external_frame g2 (frame3.mono (by decide))
  have state3 := state2.geometry_frame g3.ready frame3.memory (frame3.tapes 4 (by decide))
    (fun k _ kout _=>frame3.tapes k (by simp only [Finset.mem_singleton];omega))
    (word_of_eq (frame3.tapes 999 (by decide)) state2.outputIndex)
  have cbits : count.bits.length ≤ B := by
    rw [←hcount]
    have hslt : start<n := by omega
    simpa only [GeometryOutput.arrayValue,dite_eq_left hslt] using (hfit ⟨start,hslt⟩).trans hB
  refine ⟨c0+(c1+(c2+(6*lastWord.length+4))),t,b,_,e0.seq (e1.seq (e2.seq e3)),?_,g3,?_,state3,cf1,done1,?_,blank3,?_⟩
  · rw [len] at hc1
    rw [len1,len]
    have loopBound := hc1.trans (Nat.add_le_add
      (Nat.mul_le_mul (show count-2+1 ≤ count+1 by omega) (by omega : 13*count.bits.length+15 ≤ 13*B+15))
      (Nat.mul_le_mul_right (costBound P B M) (show count-2 ≤ count by omega)))
    rw [GeometryOutput.tripleTargets_length] at hc2
    unfold pathCost
    nlinarith only [hc0,hc2,loopBound,cbits,Nat.zero_le B]
  · rw [GeometryOutput.readPlanValues_cursor,GeometryOutput.tripleTargets_length,ix1];omega
  · intro k hk;rw [frame3.memory,f2.memory];exact mem1 k hk
  · intro k hk
    have cases : k=972 ∨ k=988 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hk
    exact (frame3.tapes k (by simp only [Finset.mem_singleton];omega)).trans
      ((f2.tapes k (by omega) (by rcases cases with rfl|rfl <;> decide)).trans
        ((keep1 k hk).trans (keep0 k (by omega) (by rcases cases with rfl|rfl <;> decide))))

#print axioms path_executes
end Maxwell.Continuum.RationalDataflow.WellInternalGeometry
