import Maxwell.Continuum.WellMediatorLoop
import Maxwell.Continuum.StoredGeometryPathSetup
import Maxwell.Cost.Structured.CounterClear

/-! A mediator path reads its actual length header and first point,
traverses exactly its adjacent pairs, then clears the padded counter. -/
namespace Maxwell.Continuum.RationalDataflow.WellMediatorGeometry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open WellStrengthPass
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def pathCode : Code := .seq (GeometryOutput.pathSetupCode 1) (.seq loopCode (.call (TapeOps.clear 973)))

def pathCost (P B M count : ℕ) : ℕ :=
  2^26*(B+3)^2+(count+1)*(13*B+15)+count*costBound P B M+6*B+4

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
    (denominator : ∀j<count-1,(v 1).value+target data (start+1+3*j) v ≠ 0)
    (a : PartArray.Table J) (config : Configuration a P B M boundary)
    (harray : base+n*width ≤ boundary) (hcapacity : first+(count-1) ≤ J) (hJ : J.bits.length ≤ M)
    (values : ℕ→Parts) (completed : a.CorrectPrefix values first)
    (agrees : ∀j<count-1,values (first+j)=part P data (start+1+3*j) v)
    (memory : ℕ→Bool) (saved : ∀k,k<boundary→s.val.memory k=memory k)
    (state : State a P v first s) (input : List Bool) (tape : ℕ→Bool)
    (old : List Bool) (hold : BankArray.Word s.val 973 old) (oldWidth : old.length ≤ B) :
    ∃cost t,∃a':PartArray.Table J,∃gv',Executes input tape pathCode cost s t ∧
      cost ≤ pathCost P B M count ∧ GeometryOutput.Context data base width B clock constants gv' t ∧
      gv' 971=start+1+3*count ∧ State a' P v (first+(count-1)) t ∧ Configuration a' P B M boundary ∧
      a'.CorrectPrefix values (first+(count-1)) ∧ (∀k,k<boundary→t.val.memory k=memory k) ∧
      Blank t.val 973 ∧ (∀k,k∈({972,988}:Finset ℕ)→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,word,origin,w,e0,hc0,g0,ix,prev,word0,len,val0,_,keep0⟩ :=
    GeometryOutput.pathSetup_executes g hw hB hlen hn hfit hb hv ho start count 1 hcursor
      (by omega) hcount (by omega) (by decide) old hold oldWidth input tape
  have memory0 : u.val.memory=s.val.memory := e0.protectsMemory (by decide)
  have state0 := state.geometry_frame g0.ready memory0 (e0.protectsTape 4 (by decide))
    (fun k hk kout _=>keep0 k hk (by simp only [Finset.mem_insert,Finset.mem_singleton];omega))
    (word_of_eq (keep0 999 (by decide) (by decide)) state.outputIndex)
  obtain ⟨c1,z,b,w',lastWord,e1,hc1,g1,ix1,_,state1,cf1,done1,mem1,word1,len1,keep1⟩ :=
    loop_executes g0 hw hB hlen hn hfit hb hv ho (start+1) (count-1) first (by omega) (by omega)
      prev v canonical hW hP rvwidth good scale denominator a config harray hcapacity hJ values completed agrees
      memory (by intro k hk;rw [memory0];exact saved k hk) state0 input tape word origin val0 word0
  obtain ⟨t,e2,blank2,frame2⟩ := RuntimeCounter.clear_executes 973 input tape lastWord origin z word1
  have g2 := geometry_external_frame g1 (frame2.mono (by decide))
  have state2 := state1.geometry_frame g2.ready frame2.memory (frame2.tapes 4 (by decide))
    (fun k _ kout _=>frame2.tapes k (by simp only [Finset.mem_singleton];omega))
    (word_of_eq (frame2.tapes 999 (by decide)) state1.outputIndex)
  have cbits : count.bits.length ≤ B := by
    rw [←hcount]
    have hslt : start<n := by omega
    simpa only [GeometryOutput.arrayValue,dite_eq_left hslt] using (hfit ⟨start,hslt⟩).trans hB
  refine ⟨c0+(c1+(6*lastWord.length+4)),t,b,w',e0.seq (e1.seq e2),?_,g2,?_,state2,cf1,done1,?_,blank2,?_⟩
  · rw [len] at hc1
    rw [len1,len]
    have loopBound := hc1.trans (Nat.add_le_add
      (Nat.mul_le_mul (show count-1+1 ≤ count+1 by omega) (by omega : 13*count.bits.length+15 ≤ 13*B+15))
      (Nat.mul_le_mul_right (costBound P B M) (show count-1 ≤ count by omega)))
    unfold pathCost
    omega
  · rw [ix1];omega
  · intro k hk;rw [frame2.memory];exact mem1 k hk
  · intro k hk
    have cases : k=972 ∨ k=988 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hk
    exact (frame2.tapes k (by simp only [Finset.mem_singleton];omega)).trans
      ((keep1 k hk).trans (keep0 k (by omega) (by rcases cases with rfl|rfl <;> decide)))

#print axioms path_executes
end Maxwell.Continuum.RationalDataflow.WellMediatorGeometry
