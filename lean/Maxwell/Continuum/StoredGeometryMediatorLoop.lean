import Maxwell.Continuum.StoredGeometryMediator

/-! Fixed adjacent-pair traversal of one chronological path. Its input is
one previously read point and a runtime remaining-edge counter. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def mediatorStream {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (start count : ℕ) : List Bool :=
  (List.range count).flatMap (fun j=>mediatorBits values constants (start+3*j))

theorem mediatorStream_succ {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (start count : ℕ) :
    mediatorStream values constants start (count+1)=mediatorStream values constants start count++
      mediatorBits values constants (start+3*count) := by simp [mediatorStream,List.range_succ]

def mediatorLoopCode : Code := RationalDataflow.countedProgram 973 mediatorStepCode

theorem mediatorLoop_executes {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (h : Context values base width B clock constants v s)
    (hw : 0<width) (hB : width≤B) (hlen : clock.length=width) (hn : n.bits.length≤B)
    (hfit : ∀i,(values.get i).bits.length≤width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (start count : ℕ) (hstart : v 971=start+3) (hspan : start+3*(count+1)≤n)
    (hp : ∀j:Fin 3,v (976+j.val)=arrayValue values (start+j.val))
    (hc : ∀j<count,∀k,(mediatorCoordinate values constants (start+3*j) k).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hx : addressValue xs=count) (hword : s.val.tapes 973=BitTape.shifted xs origin) :
    ∃cost t word w,Executes input tape mediatorLoopCode cost s t ∧
      cost≤(count+1)*(13*xs.length+15)+count*(2^30*(B+3)^2) ∧
      Context values base width B clock constants w t ∧ w 971=start+3*(count+1) ∧
      (∀j:Fin 3,w (976+j.val)=arrayValue values (start+3*count+j.val)) ∧
      t.val.output=(mediatorStream values constants start count).reverse++s.val.output ∧
      t.val.tapes 973=BitTape.shifted word origin ∧ word.length=xs.length ∧
      (∀k,10 ≤ k → k∉({973,971,976,977,978,979,980,981,987}:Finset ℕ) → t.val.tapes k=s.val.tapes k) := by
  let keep : Store→Prop := fun t=>∀k,10 ≤ k → k∉({973,971,976,977,978,979,980,981,987}:Finset ℕ) →
    t.val.tapes k=s.val.tapes k
  let inv : ℕ→Store→Prop := fun r t=>r≤count ∧ ∃w,
    Context values base width B clock constants w t ∧ w 971=start+3*((count-r)+1) ∧
      (∀j:Fin 3,w (976+j.val)=arrayValue values (start+3*(count-r)+j.val)) ∧
      t.val.output=(mediatorStream values constants start (count-r)).reverse++s.val.output ∧ keep t
  have stable : ∀r a b,CountedShifted.Frame 973 a b→inv r a→inv r b := by
    intro r a b f hh
    obtain ⟨w,cw,ix,prev,out,old⟩ := hh.2
    refine ⟨hh.1,w,cw.count_frame 973 (by decide) f,ix,prev,f.2.2.2.2.1.trans out,?_⟩
    intro k hk hnot
    have hkc : k≠973 := by intro he;subst k;exact hnot (by simp)
    exact (f.2.2.2.2.2.1 k hkc).trans (old k hk hnot)
  have step : ∀r ys a,inv (r+1) a→a.val.tapes 973=BitTape.shifted ys origin→
      addressValue ys=r→ys.length=xs.length→
      ∃c b,Executes input tape mediatorStepCode c a b ∧ inv r b ∧
        b.val.tapes 973=BitTape.shifted ys origin ∧ c≤2^30*(B+3)^2 := by
    intro r ys a hh word _ _
    obtain ⟨w,cw,ix,prev,out,old⟩ := hh.2
    have hj : count-(r+1)<count := by have := hh.1;omega
    have he : count-(r+1)+1=count-r := by have := hh.1;omega
    have hindex : w 971=(start+3*(count-(r+1)))+3 := by rw [ix];omega
    have hs' : start+3*(count-(r+1))+6≤n := by omega
    obtain ⟨c,b,w',ex,hcst,cb,ib,pb,ob,fb⟩ := mediatorStep_executes cw hw hB hlen hn hfit hb hv ho
      (start+3*(count-(r+1))) hindex hs' prev (hc _ hj) input tape
    refine ⟨c,b,ex,⟨by omega,w',cb,?_,?_,?_,?_⟩,?_,hcst⟩
    · rw [ib];omega
    · intro j;rw [pb];congr 2;omega
    · rw [ob,out,←he,mediatorStream_succ,List.reverse_append,List.append_assoc]
    · intro k hk hnot
      have hk' : k∉({971,976,977,978,979,980,981,987}:Finset ℕ) := by
        intro hm;exact hnot (Finset.mem_insert_of_mem hm)
      exact (fb k hk hk').trans (old k hk hnot)
    · exact (fb 973 (by decide) (by decide)).trans word
  have initial : inv count s := by
    refine ⟨le_rfl,v,h,?_,?_,?_,fun _ _ _=>rfl⟩
    · simpa only [Nat.sub_self,Nat.zero_add,Nat.mul_one] using hstart
    · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hp
    · simp only [Nat.sub_self,mediatorStream,List.range_zero,List.flatMap_nil,List.reverse_nil,List.nil_append]
  obtain ⟨cost,t,word,ex,final,wt,wl,_,cb⟩ := RationalDataflow.counted_executes_sized 973 origin
    mediatorStepCode input tape xs.length inv (fun _=>2^30*(B+3)^2) stable step count xs s hx hword rfl initial
  obtain ⟨w,cw,ix,prev,out,keepw⟩ := final.2
  refine ⟨cost,t,word,w,ex,?_,cw,?_,?_,?_,wt,wl,keepw⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using cb
  · simpa only [Nat.sub_zero] using ix
  · simpa only [Nat.sub_zero] using prev
  · simpa only [Nat.sub_zero] using out

#print axioms mediatorLoop_executes
end Maxwell.Continuum.GeometryOutput
