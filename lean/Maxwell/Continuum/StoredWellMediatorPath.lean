import Maxwell.Continuum.StoredWellInternalPath

/-! The complete mediator pass reads each adjacent pair once and emits
its midpoint well together with the corresponding strength and payloads. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def mediatorPathCode : Code := .seq (GeometryOutput.pathSetupCode 1) mediatorLoopCode

theorem mediatorPath_executes {n base width BG J : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : n.bits.length≤BG)
    (hfit : ∀i,(data.get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (start count first : ℕ) (hstart : gv 971=start) (hspan : start+1+3*count≤n)
    (hcount : GeometryOutput.arrayValue data start=count) (htwo : 2≤count)
    (hstrengths : first+(count-1)≤J)
    (hcoord : ∀j<count-1,∀k,(GeometryOutput.mediatorCoordinate data constants (start+1+3*j) k).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B) (hJ : J.bits.length≤B)
    (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (old : List Bool) (hold : BankArray.Word s.val 973 old) (hOld : old.length≤BG)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t word origin w r,Executes input tape mediatorPathCode cost s t ∧
      cost≤pathCost BG B count profile template ∧
      GeometryOutput.Context data base width BG clock constants w t ∧ w 971=start+1+3*count ∧
      WellPayload.State strengths P B (first+(count-1)) profile template r t ∧
      t.val.output=(mediatorStream data constants P numerators profile template (start+1) first (count-1)).reverse++s.val.output ∧
      t.val.tapes 973=BitTape.shifted word origin ∧ word.length=count.bits.length ∧
      t.val.tapes 972=s.val.tapes 972 := by
  obtain ⟨c0,a,word0,origin,w0,e0,hc0,ga,ix,prev,pa,wa,wl,wv,oa,ka⟩ :=
    pathSetup_executes g hw hBG hlen hn hfit hb hwidth ho start count 1 hstart (by omega)
      hcount (by omega) (by decide) strengths profile template rv p old hold hOld input tape
  obtain ⟨c1,t,word,w1,r1,e1,hc1,gt,ixt,prevt,pt,ot,wt,wlen,kt⟩ :=
    mediatorLoop_executes ga hw hBG hlen hn hfit hb hwidth ho (start+1) (count-1) first
      (by omega) (by omega) hstrengths prev hcoord strengths numerators hc P B hm hP hJ
      profile template rv pa input tape word0 origin wv wa
  have countB : count.bits.length≤BG := by
    rw [←hcount]
    exact (GeometryOutput.arrayValue_bits data width hfit start).trans hBG
  refine ⟨c0+c1,t,word,origin,w1,r1,e0.seq e1,?_,gt,?_,pt,?_,wt,wlen.trans wl,kt.trans ka⟩
  · rw [wl] at hc1
    have hloop := hc1.trans (Nat.add_le_add
      (Nat.mul_le_mul (show count-1+1≤count+1 by omega) (by omega : 13*count.bits.length+15≤13*BG+15))
      (Nat.mul_le_mul_right (stepCost BG B profile template) (show count-1≤count by omega)))
    unfold pathCost
    nlinarith only [hc0,hloop,Nat.zero_le BG]
  · rw [ixt]
    omega
  · exact ot.trans (by rw [oa])

#print axioms mediatorPath_executes
end Maxwell.Continuum.WellOutput
