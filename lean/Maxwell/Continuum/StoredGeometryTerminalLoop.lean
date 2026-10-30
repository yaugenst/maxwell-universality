import Maxwell.Continuum.StoredGeometryTerminal

/-! Fixed runtime traversal of consecutive terminal triples. This serves
both the original-vertex pass and the interior of each chronological path. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def terminalStream {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (start count : ℕ) : List Bool :=
  (List.range count).flatMap (fun j=>terminalBits values constants (start+3*j))

theorem terminalStream_succ {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (start count : ℕ) :
    terminalStream values constants start (count+1)=terminalStream values constants start count++
      terminalBits values constants (start+3*count) := by simp [terminalStream,List.range_succ]

def terminalLoopCode (counter : ℕ) : Code := RationalDataflow.countedProgram counter terminalStepCode

theorem terminalLoop_executes {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (h : Context values base width B clock constants v s)
    (hw : 0<width) (hB : width≤B) (hlen : clock.length=width) (hn : n.bits.length≤B)
    (hfit : ∀i,(values.get i).bits.length≤width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (start count counter : ℕ) (hcounter : counter∈({972,973}:Finset ℕ))
    (hstart : v 971=start) (hspan : start+3*count≤n)
    (hc : ∀j<count,∀k,(terminalCoordinate values constants (start+3*j) k).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hx : addressValue xs=count) (hword : s.val.tapes counter=BitTape.shifted xs origin) :
    ∃cost t word w,Executes input tape (terminalLoopCode counter) cost s t ∧
      cost≤(count+1)*(13*xs.length+15)+count*(2^30*(B+3)^2) ∧
      Context values base width B clock constants w t ∧ w 971=start+3*count ∧
      t.val.output=(terminalStream values constants start count).reverse++s.val.output ∧
      t.val.tapes counter=BitTape.shifted word origin ∧ word.length=xs.length ∧
      (∀k,10 ≤ k → k∉({counter,971,976,977,978,987}:Finset ℕ) → t.val.tapes k=s.val.tapes k) := by
  let keep : Store→Prop := fun t=>∀k,10 ≤ k → k∉({counter,971,976,977,978,987}:Finset ℕ) →
    t.val.tapes k=s.val.tapes k
  let inv : ℕ→Store→Prop := fun r t=>r≤count ∧ ∃w,
    Context values base width B clock constants w t ∧ w 971=start+3*(count-r) ∧
      t.val.output=(terminalStream values constants start (count-r)).reverse++s.val.output ∧ keep t
  have stable : ∀r a b,CountedShifted.Frame counter a b→inv r a→inv r b := by
    intro r a b f hh
    obtain ⟨w,cw,ix,out,old⟩ := hh.2
    refine ⟨hh.1,w,cw.count_frame counter hcounter f,ix,f.2.2.2.2.1.trans out,?_⟩
    intro k hk hnot
    have hkc : k≠counter := by intro he;subst k;exact hnot (by simp)
    exact (f.2.2.2.2.2.1 k hkc).trans (old k hk hnot)
  have step : ∀r ys a,inv (r+1) a→a.val.tapes counter=BitTape.shifted ys origin→
      addressValue ys=r→ys.length=xs.length→
      ∃c b,Executes input tape terminalStepCode c a b ∧ inv r b ∧
        b.val.tapes counter=BitTape.shifted ys origin ∧ c≤2^30*(B+3)^2 := by
    intro r ys a hh word _ _
    obtain ⟨w,cw,ix,out,old⟩ := hh.2
    have hj : count-(r+1)<count := by have := hh.1;omega
    have he : count-(r+1)+1=count-r := by have := hh.1;omega
    have hs' : w 971+3≤n := by rw [ix];omega
    have hc' : ∀k,(terminalCoordinate values constants (w 971) k).bits.length≤B := by
      rw [ix];exact hc _ hj
    obtain ⟨c,b,w',ex,hcst,cb,ib,ob,fb⟩ := terminalStep_executes cw hw hB hlen hn hfit hb hv ho
      hs' hc' input tape
    have hcset : counter=972 ∨ counter=973 := by
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hcounter
    refine ⟨c,b,ex,⟨by omega,w',cb,?_,?_,?_⟩,?_,hcst⟩
    · rw [ib,ix];omega
    · rw [ob,ix,out,←he,terminalStream_succ,List.reverse_append,List.append_assoc]
    · intro k hk hnot
      have hk' : k∉({971,976,977,978,987}:Finset ℕ) := by
        intro hm;exact hnot (Finset.mem_insert_of_mem hm)
      exact (fb k hk hk').trans (old k hk hnot)
    · exact (fb counter (by omega) (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)).trans word
  have initial : inv count s := by
    refine ⟨le_rfl,v,h,?_,?_,fun _ _ _=>rfl⟩
    · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hstart
    · simp only [Nat.sub_self,terminalStream,List.range_zero,List.flatMap_nil,List.reverse_nil,List.nil_append]
  obtain ⟨cost,t,word,ex,final,wt,wl,_,cb⟩ := RationalDataflow.counted_executes_sized counter origin
    terminalStepCode input tape xs.length inv (fun _=>2^30*(B+3)^2) stable step count xs s hx hword rfl initial
  obtain ⟨w,cw,ix,out,keepw⟩ := final.2
  refine ⟨cost,t,word,w,ex,?_,cw,?_,?_,wt,wl,keepw⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using cb
  · simpa only [Nat.sub_zero] using ix
  · simpa only [Nat.sub_zero] using out

#print axioms terminalLoop_executes
end Maxwell.Continuum.GeometryOutput
