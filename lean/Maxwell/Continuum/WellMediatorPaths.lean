import Maxwell.Continuum.WellMediatorPath
import Maxwell.Continuum.SourceGeometryPathCounts

/-! The outer countdown follows the actual packed path offsets. Every
path extends the existing strength prefix by its stored length minus one. -/
namespace Maxwell.Continuum.RationalDataflow.WellMediatorGeometry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration Maxwell.Logical.Routing
open WellStrengthPass
open scoped BigOperators
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def pathsCode : Code := CountedShifted.code 972 pathCode

theorem pathCost_mono (P B M a b : ℕ) (h : a ≤ b) : pathCost P B M a ≤ pathCost P B M b := by
  unfold pathCost
  nlinarith [Nat.zero_le (costBound P B M)]

theorem paths_executes {V E base width B P M J boundary : ℕ} (saved : SourceEmission.Geometry V E)
    {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context (packedVector saved) base width B clock constants gv s)
    (hw : 0<width) (hB : width ≤ B) (hlen : clock.length=width) (hn : (packedLength saved).bits.length ≤ B)
    (hfit : ∀i,((packedVector saved).get i).bits.length ≤ width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (first bound : ℕ) (hstart : gv 971=3*V)
    (htwo : ∀i:Fin E,2 ≤ (saved.paths.get i).length) (hbound : ∀i:Fin E,(saved.paths.get i).length ≤ bound)
    (v : ℕ→Parts) (canonical : WellStrengthReset.canonical v=v)
    (hW : 4 ≤ B) (hP : (2^P).bits.length ≤ B) (rvwidth : WidthBank WellStrength.bank B v)
    (good : Good WellStrength.bank v) (scale : (v 4).value ≠ 0)
    (denominator : ∀i:Fin E,∀j<(saved.paths.get i).length-1,
      (v 1).value+target (packedVector saved) (pathOffset saved i.val+1+3*j) v ≠ 0)
    (a : PartArray.Table J) (config : Configuration a P B M boundary)
    (harray : base+packedLength saved*width ≤ boundary)
    (hcapacity : first+pathPrefix saved 1 E ≤ J) (hJ : J.bits.length ≤ M)
    (values : ℕ→Parts) (completed : a.CorrectPrefix values first)
    (agrees : ∀i:Fin E,∀j<(saved.paths.get i).length-1,
      values (first+pathPrefix saved 1 i.val+j)=part P (packedVector saved) (pathOffset saved i.val+1+3*j) v)
    (memory : ℕ→Bool) (preserved : ∀k,k<boundary→s.val.memory k=memory k)
    (state : State a P v first s) (inner : Blank s.val 973) (input : List Bool) (tape : ℕ→Bool)
    (xs : List Bool) (origin : ℤ) (hx : addressValue xs=E) (word : s.val.tapes 972=BitTape.shifted xs origin) :
    ∃cost t,∃a':PartArray.Table J,∃gv' finalWord,Executes input tape pathsCode cost s t ∧
      cost ≤ (E+1)*(13*xs.length+15)+E*pathCost P B M bound ∧
      GeometryOutput.Context (packedVector saved) base width B clock constants gv' t ∧ gv' 971=packedLength saved ∧
      State a' P v (first+pathPrefix saved 1 E) t ∧ Configuration a' P B M boundary ∧
      a'.CorrectPrefix values (first+pathPrefix saved 1 E) ∧
      (∀k,k<boundary→t.val.memory k=memory k) ∧ Blank t.val 973 ∧
      t.val.tapes 972=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      t.val.tapes 988=s.val.tapes 988 := by
  let inv : ℕ→Store→Prop := fun remaining t=>remaining ≤ E ∧ ∃w,∃b:PartArray.Table J,
    GeometryOutput.Context (packedVector saved) base width B clock constants w t ∧
    w 971=pathOffset saved (E-remaining) ∧ State b P v (first+pathPrefix saved 1 (E-remaining)) t ∧
    Configuration b P B M boundary ∧ b.CorrectPrefix values (first+pathPrefix saved 1 (E-remaining)) ∧
    (∀k,k<boundary→t.val.memory k=memory k) ∧ Blank t.val 973 ∧ t.val.tapes 988=s.val.tapes 988
  have stable : ∀q u t,CountedShifted.Frame 972 u t→inv q u→inv q t := by
    intro q u t f ⟨hq,w,b,gu,ix,st,cf,done,mem,blank,keep⟩
    have gt := gu.count_frame 972 (by decide) f
    have st' := st.geometry_frame gt.ready f.2.2.1 (f.2.2.2.2.2.1 4 (by decide))
      (fun k _ kout _=>f.2.2.2.2.2.1 k (by omega))
      (word_of_eq (f.2.2.2.2.2.1 999 (by decide)) st.outputIndex)
    refine ⟨hq,w,b,gt,ix,st',cf,done,?_,blank_of_eq (f.2.2.2.2.2.1 973 (by decide)) blank,
      (f.2.2.2.2.2.1 988 (by decide)).trans keep⟩
    intro k hk;rw [f.2.2.1];exact mem k hk
  have step : ∀q ys u,inv (q+1) u→u.val.tapes 972=BitTape.shifted ys origin→addressValue ys=q→
      ∃c t,Executes input tape pathCode c u t ∧ inv q t ∧
        t.val.tapes 972=BitTape.shifted ys origin ∧ c ≤ pathCost P B M bound := by
    intro q ys u ⟨hq,w,b,gu,ix,st,cf,done,mem,blank,keep⟩ counter _
    let i : Fin E := ⟨E-(q+1),by omega⟩
    have index : i.val+1=E-q := by dsimp [i];omega
    have capacity : first+pathPrefix saved 1 i.val+((saved.paths.get i).length-1) ≤ J := by
      rw [Nat.add_assoc,←pathPrefix_succ saved 1 i]
      exact (Nat.add_le_add_left (pathPrefix_le_end saved 1 (i.val+1)) first).trans hcapacity
    obtain ⟨c,t,b',w',e,hc,gt,it,st',cf',done',mem',blank',ft⟩ := path_executes gu hw hB hlen hn hfit hb hv ho
      (pathOffset saved i.val) (saved.paths.get i).length (first+pathPrefix saved 1 i.val)
      ix (pathOffset_span saved i) (path_length_lookup saved i) (htwo i) v canonical hW hP rvwidth good scale
      (denominator i) b cf harray capacity hJ values done (agrees i) memory mem st input tape []
      ((zero_word_iff_blank u.val 973).mpr blank) (by simp)
    refine ⟨c,t,e,⟨by omega,w',b',gt,?_,?_,cf',?_,mem',blank',(ft 988 (by decide)).trans keep⟩,
      (ft 972 (by decide)).trans counter,hc.trans (pathCost_mono P B M _ bound (hbound i))⟩
    · rw [it,←pathOffset_succ saved i,index]
    · rw [←index,pathPrefix_succ saved 1 i]
      simpa only [Nat.add_assoc] using st'
    · rw [←index,pathPrefix_succ saved 1 i]
      simpa only [Nat.add_assoc] using done'
  have initial : inv E s := by
    refine ⟨le_rfl,gv,a,g,?_,?_,config,?_,preserved,inner,rfl⟩
    · simpa only [Nat.sub_self,pathOffset_zero] using hstart
    · simpa only [Nat.sub_self,pathPrefix_zero,Nat.add_zero] using state
    · simpa only [Nat.sub_self,pathPrefix_zero,Nat.add_zero] using completed
  obtain ⟨c,t,finalWord,e,ht,word',length,_,hc⟩ := CountedShifted.executes 972 origin pathCode input tape
    inv (fun _=>pathCost P B M bound) stable step E xs s hx word initial
  obtain ⟨_,w,b,gt,ix,st,cf,done,mem,blank,keep⟩ := ht
  refine ⟨c,t,b,w,finalWord,e,?_,gt,?_,?_,cf,?_,mem,blank,word',length,keep⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hc
  · simpa only [Nat.sub_zero,pathOffset_end] using ix
  · simpa only [Nat.sub_zero] using st
  · simpa only [Nat.sub_zero] using done

#print axioms paths_executes
end Maxwell.Continuum.RationalDataflow.WellMediatorGeometry
