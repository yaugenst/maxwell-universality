import Maxwell.Continuum.StoredWellPathSetup
import Maxwell.Continuum.StoredGeometryBounds

/-! A complete path-interior pass skips its two original endpoints and
emits the complete well record for each chronological internal vertex. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def pathCost (BG B count : ℕ) (profile template : List Bool) : ℕ :=
  2^27*(BG+3)^2+(count+1)*(13*BG+15)+count*stepCost BG B profile template

def internalPathCode : Code := .seq (GeometryOutput.pathSetupCode 2)
  (.seq (terminalLoopCode 973) (GeometryOutput.readPlanCode (GeometryOutput.tripleTargets false)))

theorem internalPath_executes {n base width BG J : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : n.bits.length≤BG)
    (hfit : ∀i,(data.get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (start count first : ℕ) (hstart : gv 971=start) (hspan : start+1+3*count≤n)
    (hcount : GeometryOutput.arrayValue data start=count) (htwo : 2≤count)
    (hstrengths : first+(count-2)≤J)
    (hcoord : ∀j<count-2,∀k,(GeometryOutput.terminalCoordinate data constants (start+4+3*j) k).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B) (hJ : J.bits.length≤B)
    (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (old : List Bool) (hold : BankArray.Word s.val 973 old) (hOld : old.length≤BG)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t word origin w r,Executes input tape internalPathCode cost s t ∧
      cost≤pathCost BG B count profile template ∧
      GeometryOutput.Context data base width BG clock constants w t ∧ w 971=start+1+3*count ∧
      WellPayload.State strengths P B (first+(count-2)) profile template r t ∧
      t.val.output=(terminalStream data constants P numerators profile template (start+4) first (count-2)).reverse++s.val.output ∧
      t.val.tapes 973=BitTape.shifted word origin ∧ word.length=count.bits.length ∧
      t.val.tapes 972=s.val.tapes 972 := by
  obtain ⟨c0,a,word0,origin,w0,e0,hc0,ga,ix,prev,pa,wa,wl,wv,oa,ka⟩ :=
    pathSetup_executes g hw hBG hlen hn hfit hb hwidth ho start count 2 hstart (by omega)
      hcount htwo le_rfl strengths profile template rv p old hold hOld input tape
  obtain ⟨c1,b,word,w1,r1,e1,hc1,gb,ixb,pb,ob,wb,wlen,kb⟩ :=
    terminalLoop_executes ga hw hBG hlen hn hfit hb hwidth ho (start+4) (count-2) first 973 (by decide)
      ix (by omega) hstrengths hcoord strengths numerators hc P B hm hP hJ profile template rv pa input tape
      word0 origin wv wa
  obtain ⟨c2,t,e2,hc2,gt,ft⟩ := gb.read_plan (GeometryOutput.tripleTargets false)
    (GeometryOutput.tripleTargets_valid false) (GeometryOutput.tripleTargets_fixed false)
    hw hBG hlen hn hfit hb hwidth ho
    (by rw [GeometryOutput.tripleTargets_length,ixb];omega) input tape
  have pt := pb.geometry_frame gt.ready ft.memory (fun k hk hr=>ft.tapes k hk (by
    simp only [GeometryOutput.tripleTargets,Bool.false_eq_true,ite_false,List.toFinset_cons,
      List.toFinset_nil,Finset.union_singleton,Finset.mem_insert,
      Finset.notMem_empty,or_false];omega))
  have countB : count.bits.length≤BG := by
    rw [←hcount]
    exact (GeometryOutput.arrayValue_bits data width hfit start).trans hBG
  refine ⟨c0+(c1+c2),t,word,origin,_,r1,e0.seq (e1.seq e2),?_,gt,?_,pt,?_,?_,wlen.trans wl,?_⟩
  · rw [wl] at hc1
    rw [GeometryOutput.tripleTargets_length] at hc2
    have hloop := hc1.trans (Nat.add_le_add
      (Nat.mul_le_mul (show count-2+1≤count+1 by omega) (by omega : 13*count.bits.length+15≤13*BG+15))
      (Nat.mul_le_mul_right (stepCost BG B profile template) (show count-2≤count by omega)))
    unfold pathCost
    nlinarith only [hc0,hc2,hloop,Nat.zero_le BG]
  · rw [GeometryOutput.readPlanValues_cursor,GeometryOutput.tripleTargets_length,ixb]
    omega
  · exact ft.output.trans (ob.trans (by rw [oa]))
  · exact (ft.tapes 973 (by decide) (by decide)).trans wb
  · exact (ft.tapes 972 (by decide) (by decide)).trans ((kb 972 (by decide) (by decide)).trans ka)

#print axioms internalPath_executes
end Maxwell.Continuum.WellOutput
