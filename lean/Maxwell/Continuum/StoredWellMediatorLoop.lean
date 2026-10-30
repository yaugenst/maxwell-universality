import Maxwell.Continuum.StoredWellTerminalLoop

/-! Adjacent-pair well traversal with the actual strength and polynomial
payload emitted immediately after every computed midpoint record. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def mediatorStream {n : ℕ} (data : Vector ℕ n) (constants : ℕ→ℕ)
    (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) (start first count : ℕ) : List Bool :=
  (List.range count).flatMap (fun j=>GeometryOutput.mediatorBits data constants (start+3*j)++
    WellPayload.bits P (numerators (first+j)) profile template)

theorem mediatorStream_succ {n : ℕ} (data : Vector ℕ n) (constants : ℕ→ℕ)
    (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) (start first count : ℕ) :
    mediatorStream data constants P numerators profile template start first (count+1)=
      mediatorStream data constants P numerators profile template start first count++
        (GeometryOutput.mediatorBits data constants (start+3*count)++
          WellPayload.bits P (numerators (first+count)) profile template) := by
  simp [mediatorStream,List.range_succ]

def mediatorLoopCode : Code := countedProgram 973 mediatorCode

theorem mediatorLoop_executes {n base width BG J : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : n.bits.length≤BG)
    (hfit : ∀i,(data.get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (start count first : ℕ) (hstart : gv 971=start+3) (hspan : start+3*(count+1)≤n)
    (hstrengths : first+count≤J)
    (hprev : ∀j:Fin 3,gv (976+j.val)=GeometryOutput.arrayValue data (start+j.val))
    (hcoord : ∀j<count,∀k,(GeometryOutput.mediatorCoordinate data constants (start+3*j) k).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B) (hJ : J.bits.length≤B)
    (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hx : addressValue xs=count) (hword : s.val.tapes 973=BitTape.shifted xs origin) :
    ∃cost t word w r,Executes input tape mediatorLoopCode cost s t ∧
      cost≤(count+1)*(13*xs.length+15)+count*stepCost BG B profile template ∧
      GeometryOutput.Context data base width BG clock constants w t ∧ w 971=start+3*(count+1) ∧
      (∀j:Fin 3,w (976+j.val)=GeometryOutput.arrayValue data (start+3*count+j.val)) ∧
      WellPayload.State strengths P B (first+count) profile template r t ∧
      t.val.output=(mediatorStream data constants P numerators profile template start first count).reverse++s.val.output ∧
      t.val.tapes 973=BitTape.shifted word origin ∧ word.length=xs.length ∧ t.val.tapes 972=s.val.tapes 972 := by
  let inv : ℕ→Store→Prop := fun remaining t=>remaining≤count ∧ ∃w r,
    GeometryOutput.Context data base width BG clock constants w t ∧ w 971=start+3*((count-remaining)+1) ∧
    (∀j:Fin 3,w (976+j.val)=GeometryOutput.arrayValue data (start+3*(count-remaining)+j.val)) ∧
    WellPayload.State strengths P B (first+(count-remaining)) profile template r t ∧
    t.val.output=(mediatorStream data constants P numerators profile template start first (count-remaining)).reverse++s.val.output ∧
    t.val.tapes 972=s.val.tapes 972
  have stable : ∀q a b,CountedShifted.Frame 973 a b→inv q a→inv q b := by
    intro q a b f h
    obtain ⟨w,r,ga,ix,prev,pa,out,keepa⟩ := h.2
    have gb := ga.count_frame 973 (by decide) f
    have pb := pa.geometry_frame gb.ready f.2.2.1 (fun k _ hr=>f.2.2.2.2.2.1 k (by omega))
    exact ⟨h.1,w,r,gb,ix,prev,pb,f.2.2.2.2.1.trans out,(f.2.2.2.2.2.1 972 (by decide)).trans keepa⟩
  have step : ∀q ys a,inv (q+1) a→a.val.tapes 973=BitTape.shifted ys origin→
      addressValue ys=q→ys.length=xs.length→
      ∃c b,Executes input tape mediatorCode c a b ∧ inv q b ∧
        b.val.tapes 973=BitTape.shifted ys origin ∧ c≤stepCost BG B profile template := by
    intro q ys a hh word _ _
    obtain ⟨w,r,ga,ix,prev,pa,out,keepa⟩ := hh.2
    have hj : count-(q+1)<count := by have := hh.1;omega
    have he : count-(q+1)+1=count-q := by have := hh.1;omega
    let i : Fin J := ⟨first+(count-(q+1)),by omega⟩
    have hi : i.val.bits.length≤B := by
      apply le_trans _ hJ
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size i.isLt.le
    obtain ⟨c,b,w',ex,hcst,gb,ib,pb,prb,ob,fb⟩ := mediator_executes ga hw hBG hlen hn hfit hb hwidth ho
      (start+3*(count-(q+1))) (by rw [ix];omega) (by omega) prev (hcoord _ hj)
      strengths numerators hc P B hm hP profile template i hi r pa input tape
    refine ⟨c,b,ex,⟨by omega,w',Function.update r 0 (strengths.get i),gb,?_,?_,?_,?_,(fb 972 (by decide)).trans keepa⟩,
      (fb 973 (by decide)).trans word,hcst⟩
    · rw [ib];omega
    · intro j;rw [pb];congr 2;omega
    · convert prb using 1
      change first+(count-q)=first+(count-(q+1))+1
      omega
    · rw [ob,out,←he,mediatorStream_succ]
      simp only [List.reverse_append,List.append_assoc]
      rfl
  have initial : inv count s := by
    refine ⟨le_rfl,gv,rv,g,?_,?_,?_,?_,rfl⟩
    · simpa only [Nat.sub_self,Nat.zero_add,Nat.mul_one] using hstart
    · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hprev
    · simpa only [Nat.sub_self,Nat.add_zero] using p
    · simp only [Nat.sub_self,mediatorStream,List.range_zero,List.flatMap_nil,List.reverse_nil,List.nil_append]
  obtain ⟨cost,t,word,ex,hfinal,wt,wl,_,cb⟩ := counted_executes_sized 973 origin mediatorCode
    input tape xs.length inv (fun _=>stepCost BG B profile template) stable step count xs s hx hword rfl initial
  obtain ⟨w,r,gt,ix,prev,pt,out,keepw⟩ := hfinal.2
  refine ⟨cost,t,word,w,r,ex,?_,gt,?_,?_,?_,?_,wt,wl,keepw⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using cb
  · simpa only [Nat.sub_zero] using ix
  · simpa only [Nat.sub_zero] using prev
  · simpa only [Nat.sub_zero] using pt
  · simpa only [Nat.sub_zero] using out

#print axioms mediatorLoop_executes
end Maxwell.Continuum.WellOutput
