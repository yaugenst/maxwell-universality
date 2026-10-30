import Maxwell.Continuum.StoredWellStep

/-! Full terminal-well records are emitted inside the actual counted
geometry loop, including every strength and polynomial payload copy. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def terminalStream {n : ℕ} (data : Vector ℕ n) (constants : ℕ→ℕ)
    (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) (start first count : ℕ) : List Bool :=
  (List.range count).flatMap (fun j=>GeometryOutput.terminalBits data constants (start+3*j)++
    WellPayload.bits P (numerators (first+j)) profile template)

theorem terminalStream_succ {n : ℕ} (data : Vector ℕ n) (constants : ℕ→ℕ)
    (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) (start first count : ℕ) :
    terminalStream data constants P numerators profile template start first (count+1)=
      terminalStream data constants P numerators profile template start first count++
        (GeometryOutput.terminalBits data constants (start+3*count)++
          WellPayload.bits P (numerators (first+count)) profile template) := by
  simp [terminalStream,List.range_succ]

def terminalLoopCode (counter : ℕ) : Code := countedProgram counter terminalCode

theorem terminalLoop_executes {n base width BG J : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : n.bits.length≤BG)
    (hfit : ∀i,(data.get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (start count first counter : ℕ) (hcounter : counter∈({972,973}:Finset ℕ))
    (hstart : gv 971=start) (hspan : start+3*count≤n) (hstrengths : first+count≤J)
    (hcoord : ∀j<count,∀k,(GeometryOutput.terminalCoordinate data constants (start+3*j) k).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B) (hJ : J.bits.length≤B)
    (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hx : addressValue xs=count) (hword : s.val.tapes counter=BitTape.shifted xs origin) :
    ∃cost t word w r,Executes input tape (terminalLoopCode counter) cost s t ∧
      cost≤(count+1)*(13*xs.length+15)+count*stepCost BG B profile template ∧
      GeometryOutput.Context data base width BG clock constants w t ∧ w 971=start+3*count ∧
      WellPayload.State strengths P B (first+count) profile template r t ∧
      t.val.output=(terminalStream data constants P numerators profile template start first count).reverse++s.val.output ∧
      t.val.tapes counter=BitTape.shifted word origin ∧ word.length=xs.length ∧
      (∀k∈({972,973}:Finset ℕ),k≠counter→t.val.tapes k=s.val.tapes k) := by
  let keep : Store→Prop := fun t=>∀k∈({972,973}:Finset ℕ),k≠counter→t.val.tapes k=s.val.tapes k
  let inv : ℕ→Store→Prop := fun remaining t=>remaining≤count ∧ ∃w r,
    GeometryOutput.Context data base width BG clock constants w t ∧ w 971=start+3*(count-remaining) ∧
    WellPayload.State strengths P B (first+(count-remaining)) profile template r t ∧
    t.val.output=(terminalStream data constants P numerators profile template start first (count-remaining)).reverse++s.val.output ∧
    keep t
  have stable : ∀q a b,CountedShifted.Frame counter a b→inv q a→inv q b := by
    intro q a b f h
    obtain ⟨w,r,ga,ix,pa,out,keepa⟩ := h.2
    have gb := ga.count_frame counter hcounter f
    have pb := pa.geometry_frame gb.ready f.2.2.1 (fun k _ hr=>
      f.2.2.2.2.2.1 k (by simp only [Finset.mem_insert,Finset.mem_singleton] at hcounter;omega))
    exact ⟨h.1,w,r,gb,ix,pb,f.2.2.2.2.1.trans out,
      fun k hk hne=>(f.2.2.2.2.2.1 k hne).trans (keepa k hk hne)⟩
  have step : ∀q ys a,inv (q+1) a→a.val.tapes counter=BitTape.shifted ys origin→
      addressValue ys=q→ys.length=xs.length→
      ∃c b,Executes input tape terminalCode c a b ∧ inv q b ∧
        b.val.tapes counter=BitTape.shifted ys origin ∧ c≤stepCost BG B profile template := by
    intro q ys a hh word _ _
    obtain ⟨w,r,ga,ix,pa,out,keepa⟩ := hh.2
    have hj : count-(q+1)<count := by have := hh.1;omega
    have he : count-(q+1)+1=count-q := by have := hh.1;omega
    let i : Fin J := ⟨first+(count-(q+1)),by omega⟩
    have hi : i.val.bits.length≤B := by
      apply le_trans _ hJ
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size i.isLt.le
    obtain ⟨c,b,w',ex,hcst,gb,ib,pb,ob,fb⟩ := terminal_executes ga hw hBG hlen hn hfit hb hwidth ho
      (by rw [ix];omega) (fun k=>by rw [ix];exact hcoord _ hj k)
      strengths numerators hc P B hm hP profile template i hi r pa input tape
    refine ⟨c,b,ex,⟨by omega,w',Function.update r 0 (strengths.get i),gb,?_,?_,?_,?_⟩,(fb counter hcounter).trans word,hcst⟩
    · rw [ib,ix];omega
    · convert pb using 1
      change first+(count-q)=first+(count-(q+1))+1
      omega
    · rw [ob,ix,out,←he,terminalStream_succ]
      simp only [List.reverse_append,List.append_assoc]
      rfl
    · exact fun k hk hne=>(fb k hk).trans (keepa k hk hne)
  have initial : inv count s := by
    refine ⟨le_rfl,gv,rv,g,?_,?_,?_,fun _ _ _=>rfl⟩
    · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hstart
    · simpa only [Nat.sub_self,Nat.add_zero] using p
    · simp only [Nat.sub_self,terminalStream,List.range_zero,List.flatMap_nil,List.reverse_nil,List.nil_append]
  obtain ⟨cost,t,word,ex,hfinal,wt,wl,_,cb⟩ := counted_executes_sized counter origin terminalCode
    input tape xs.length inv (fun _=>stepCost BG B profile template) stable step count xs s hx hword rfl initial
  obtain ⟨w,r,gt,ix,pt,out,keepw⟩ := hfinal.2
  refine ⟨cost,t,word,w,r,ex,?_,gt,?_,?_,?_,wt,wl,keepw⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using cb
  · simpa only [Nat.sub_zero] using ix
  · simpa only [Nat.sub_zero] using pt
  · simpa only [Nat.sub_zero] using out

#print axioms terminalLoop_executes
end Maxwell.Continuum.WellOutput
