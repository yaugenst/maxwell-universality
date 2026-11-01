import Maxwell.Continuum.WellMediatorGeometry
import Maxwell.Continuum.RationalDataflowTableWritePrefix

/-! A chronological adjacent-point loop computes every mediator strength
from packed geometry while extending the already completed table prefix. -/
namespace Maxwell.Continuum.RationalDataflow.WellMediatorGeometry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open WellStrengthPass
open scoped BigOperators
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def loopCode : Code := CountedShifted.code 973 code

theorem loop_executes {n J base width B P M boundary : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store} (g : GeometryOutput.Context data base width B clock constants gv s)
    (hw : 0<width) (hB : width ≤ B) (hlen : clock.length=width) (hn : n.bits.length ≤ B)
    (hfit : ∀i,(data.get i).bits.length ≤ width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (start count first : ℕ) (hcursor : gv 971=start+3) (hspan : start+3*(count+1) ≤ n)
    (hprev : ∀j:Fin 3,gv (976+j.val)=GeometryOutput.arrayValue data (start+j.val))
    (v : ℕ→Parts) (canonical : WellStrengthReset.canonical v=v)
    (hW : 4 ≤ B) (hP : (2^P).bits.length ≤ B) (rvwidth : WidthBank WellStrength.bank B v)
    (good : Good WellStrength.bank v) (scale : (v 4).value ≠ 0)
    (denominator : ∀j<count,(v 1).value+target data (start+3*j) v ≠ 0)
    (a : PartArray.Table J) (config : Configuration a P B M boundary)
    (harray : base+n*width ≤ boundary) (hcapacity : first+count ≤ J) (hJ : J.bits.length ≤ M)
    (values : ℕ→Parts) (completed : a.CorrectPrefix values first)
    (agrees : ∀j<count,values (first+j)=part P data (start+3*j) v)
    (memory : ℕ→Bool) (saved : ∀k,k<boundary→s.val.memory k=memory k)
    (state : State a P v first s) (input : List Bool) (tape : ℕ→Bool)
    (xs : List Bool) (origin : ℤ) (hx : addressValue xs=count)
    (word : s.val.tapes 973=BitTape.shifted xs origin) :
    ∃cost t,∃a':PartArray.Table J,∃gv' finalWord,Executes input tape loopCode cost s t ∧
      cost ≤ (count+1)*(13*xs.length+15)+count*costBound P B M ∧
      GeometryOutput.Context data base width B clock constants gv' t ∧ gv' 971=start+3*(count+1) ∧
      (∀j:Fin 3,gv' (976+j.val)=GeometryOutput.arrayValue data (start+3*count+j.val)) ∧
      State a' P v (first+count) t ∧ Configuration a' P B M boundary ∧
      a'.CorrectPrefix values (first+count) ∧ (∀k,k<boundary→t.val.memory k=memory k) ∧
      t.val.tapes 973=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      (∀k,k∈({972,988}:Finset ℕ)→t.val.tapes k=s.val.tapes k) := by
  let inv : ℕ→Store→Prop := fun remaining t=>remaining ≤ count ∧ ∃w,∃b:PartArray.Table J,
    GeometryOutput.Context data base width B clock constants w t ∧ w 971=start+3*((count-remaining)+1) ∧
    (∀j:Fin 3,w (976+j.val)=GeometryOutput.arrayValue data (start+3*(count-remaining)+j.val)) ∧
    State b P v (first+(count-remaining)) t ∧ Configuration b P B M boundary ∧
    b.CorrectPrefix values (first+(count-remaining)) ∧ (∀k,k<boundary→t.val.memory k=memory k) ∧
    ∀k,k∈({972,988}:Finset ℕ)→t.val.tapes k=s.val.tapes k
  have stable : ∀q u t,CountedShifted.Frame 973 u t→inv q u→inv q t := by
    intro q u t f ⟨hq,w,b,gu,ix,prev,st,cf,done,mem,keep⟩
    have gt := gu.count_frame 973 (by decide) f
    have st' := st.geometry_frame gt.ready f.2.2.1 (f.2.2.2.2.2.1 4 (by decide))
      (fun k _ kout _=>f.2.2.2.2.2.1 k (by omega))
      (word_of_eq (f.2.2.2.2.2.1 999 (by decide)) st.outputIndex)
    refine ⟨hq,w,b,gt,ix,prev,st',cf,done,?_,?_⟩
    · intro k hk;rw [f.2.2.1];exact mem k hk
    · intro k hk
      exact (f.2.2.2.2.2.1 k (by simp only [Finset.mem_insert,Finset.mem_singleton] at hk;omega)).trans (keep k hk)
  have step : ∀q ys u,inv (q+1) u→u.val.tapes 973=BitTape.shifted ys origin→addressValue ys=q→
      ∃c t,Executes input tape code c u t ∧ inv q t ∧
        t.val.tapes 973=BitTape.shifted ys origin ∧ c ≤ costBound P B M := by
    intro q ys u ⟨hq,w,b,gu,ix,prev,st,cf,done,mem,keep⟩ counter _
    have hj : count-(q+1)<count := by omega
    have index : count-(q+1)+1=count-q := by omega
    let i : Fin J := ⟨first+(count-(q+1)),by omega⟩
    have ibits : i.val.bits.length ≤ M := by
      apply le_trans _ hJ
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size i.isLt.le
    obtain ⟨c,t,w',e,hc,gt,it,pt,st',mt,wt,ft⟩ := executes gu hw hB hlen hn hfit hb hv ho
      (start+3*(count-(q+1))) (by rw [ix];omega) (by omega) prev v canonical hW hP rvwidth good scale
      (denominator _ hj) b i ibits cf.metadata cf.fit cf.separated
      (fun base hbase=>harray.trans (cf.above base hbase)) st input tape
    have partEq := agrees _ hj
    change values i.val=part P data (start+3*(count-(q+1))) v at partEq
    have completed' := done.next i (by rw [partEq];exact wt)
    rw [partEq] at completed'
    refine ⟨c,t,e,⟨by omega,w',b.set i (part P data (start+3*(count-(q+1))) v),gt,?_,?_,?_,cf.set _ _,?_,?_,?_⟩,
      (ft 973 (by decide)).trans counter,hc⟩
    · rw [it];omega
    · intro j;rw [pt];congr 2;omega
    · convert st' using 1
      change first+(count-q)=first+(count-(q+1))+1
      omega
    · convert completed' using 1
      change first+(count-q)=first+(count-(q+1))+1
      omega
    · intro k hk
      rw [mt,b.writeMemory_prefix _ _ _ boundary (cf.above _ (by simp))
        (cf.above _ (by simp)) (cf.above _ (by simp)) k hk]
      exact mem k hk
    · intro k hk
      exact (ft k (by simp only [Finset.mem_insert,Finset.mem_singleton] at hk ⊢;tauto)).trans (keep k hk)
  have initial : inv count s := by
    refine ⟨le_rfl,gv,a,g,?_,?_,?_,config,?_,saved,fun _ _=>rfl⟩
    · simpa only [Nat.sub_self,Nat.zero_add,Nat.mul_one] using hcursor
    · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hprev
    · simpa only [Nat.sub_self,Nat.add_zero] using state
    · simpa only [Nat.sub_self,Nat.add_zero] using completed
  obtain ⟨c,t,finalWord,e,ht,word',length,_,hc⟩ := CountedShifted.executes 973 origin code input tape
    inv (fun _=>costBound P B M) stable step count xs s hx word initial
  obtain ⟨_,w,b,gt,ix,prev,st,cf,done,mem,keep⟩ := ht
  refine ⟨c,t,b,w,finalWord,e,?_,gt,?_,?_,?_,cf,?_,mem,word',length,keep⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hc
  · simpa only [Nat.sub_zero] using ix
  · simpa only [Nat.sub_zero] using prev
  · simpa only [Nat.sub_zero] using st
  · simpa only [Nat.sub_zero] using done

#print axioms loop_executes
end Maxwell.Continuum.RationalDataflow.WellMediatorGeometry
