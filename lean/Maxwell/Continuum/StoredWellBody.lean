import Maxwell.Continuum.StoredWellPathsLoaded

/-! Complete chronological wells: original vertices, subdivision vertices,
and finally mediator edges, with all payloads interleaved on the output. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def bodyCode : Code := .seq originalCode (.seq (loadedPathsCode false) (loadedPathsCode true))

def bodyBits {v e : ℕ} (saved : SourceEmission.Geometry v e) (constants : ℕ→ℕ)
    (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) : List Bool :=
  terminalStream (packedVector saved) constants P numerators profile template 0 0 v++
  pathsStream saved constants false P numerators profile template v e++
  pathsStream saved constants true P numerators profile template (v+pathPrefix saved 2 e) e

theorem body_executes {v e base width BG : ℕ} (saved : SourceEmission.Geometry v e)
    {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context (packedVector saved) base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : (packedLength saved).bits.length≤BG)
    (hfit : ∀i,((packedVector saved).get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (hv : constants 963=v) (he : constants 964=e) (hthree : constants 969=3)
    (bound : ℕ) (htwo : ∀i:Fin e,2≤(saved.paths.get i).length) (hbound : ∀i:Fin e,(saved.paths.get i).length≤bound)
    (hterminal : ∀cursor j,(GeometryOutput.terminalCoordinate (packedVector saved) constants cursor j).bits.length≤BG)
    (hmediator : ∀cursor j,(GeometryOutput.mediatorCoordinate (packedVector saved) constants cursor j).bits.length≤BG)
    (strengths : Table (siteCount saved)) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin (siteCount saved),strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B) (hJ : (siteCount saved).bits.length≤B)
    (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B 0 profile template rv s)
    (old inner : List Bool) (hold : BankArray.Word s.val 972 old) (hOld : old.length≤BG)
    (hinner : BankArray.Word s.val 973 inner) (hInner : inner.length≤BG)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t word origin w r inner',Executes input tape bodyCode cost s t ∧
      cost≤originalCost BG B v profile template+2*loadedPathsCost BG B e bound profile template ∧
      GeometryOutput.Context (packedVector saved) base width BG clock constants w t ∧ w 971=packedLength saved ∧
      WellPayload.State strengths P B (siteCount saved) profile template r t ∧
      t.val.output=(bodyBits saved constants P numerators profile template).reverse++s.val.output ∧
      t.val.tapes 972=BitTape.shifted word origin ∧ word.length=e.bits.length ∧
      BankArray.Word t.val 973 inner' ∧ inner'.length≤BG := by
  have hsites := siteCount_eq_prefix saved
  have vB : v.bits.length≤BG := by
    have := g.wordWidth 963 (by decide)
    rw [g.fixed 963 (by decide),hv] at this
    exact this
  have eB : e.bits.length≤BG := by
    have := g.wordWidth 964 (by decide)
    rw [g.fixed 964 (by decide),he] at this
    exact this
  obtain ⟨c0,a,word0,origin0,w0,r0,e0,hc0,ga,ixa,pa,oa,wa,wl0,ka⟩ := original_executes saved g
    hw hBG hlen hn hfit hb hwidth ho hv hthree 0 (by omega) hterminal
    strengths numerators hc P B hm hP hJ profile template rv p old hold hOld input tape
  have pa' : WellPayload.State strengths P B v profile template r0 a := by simpa only [Nat.zero_add] using pa
  have ia := BankArray.word_of_eq ka hinner
  obtain ⟨c1,b,word1,origin1,w1,r1,inner1,e1,hc1,gb,ixb,pb,ob,wb,wl1,ib,il1⟩ := loadedPaths_executes saved ga
    hw hBG hlen hn hfit hb hwidth ho hv he hthree false v bound htwo hbound
    (by change v+pathPrefix saved 2 e≤siteCount saved;omega) hterminal hmediator
    strengths numerators hc P B hm hP hJ profile template r0 pa' word0 inner ⟨origin0,wa⟩
    (wl0.trans_le vB) ia hInner input tape
  obtain ⟨c2,t,word,origin,w,r,inner',e2,hc2,gt,ixt,pt,ot,wt,wl,it,il⟩ := loadedPaths_executes saved gb
    hw hBG hlen hn hfit hb hwidth ho hv he hthree true (v+pathPrefix saved 2 e) bound htwo hbound
    (by change v+pathPrefix saved 2 e+pathPrefix saved 1 e≤siteCount saved;omega) hterminal hmediator
    strengths numerators hc P B hm hP hJ profile template r1 pb word1 inner1 ⟨origin1,wb⟩
    (wl1.trans_le eB) ib il1 input tape
  refine ⟨c0+(c1+c2),t,word,origin,w,r,inner',e0.seq (e1.seq e2),by omega,gt,ixt,?_,?_,wt,wl,it,il⟩
  · change WellPayload.State strengths P B (v+pathPrefix saved 2 e+pathPrefix saved 1 e) profile template r t at pt
    rw [←hsites] at pt
    exact pt
  · rw [ot,ob,oa]
    simp only [bodyBits,List.reverse_append,List.append_assoc]

#print axioms body_executes
end Maxwell.Continuum.WellOutput
