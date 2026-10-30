import Maxwell.Continuum.StoredWellOriginals

/-! Each path pass resets the packed cursor and loads its outer counter
from the stored edge count before running the fixed traversal. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def loadedPathsCode (mediator : Bool) : Code := .seq (cursorCode true)
  (.seq (WordReplace.code 964 972) (pathsCode mediator))

def loadedPathsCost (BG B edges bound : ℕ) (profile template : List Bool) : ℕ :=
  2^23*(BG+3)^2+(21*BG+21)+(edges+1)*(13*BG+15)+edges*pathCost BG B bound profile template

theorem loadedPaths_executes {v e base width BG J : ℕ} (saved : SourceEmission.Geometry v e)
    {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context (packedVector saved) base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : (packedLength saved).bits.length≤BG)
    (hfit : ∀i,((packedVector saved).get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (hv : constants 963=v) (he : constants 964=e) (hthree : constants 969=3)
    (mediator : Bool) (first bound : ℕ)
    (htwo : ∀i:Fin e,2≤(saved.paths.get i).length) (hbound : ∀i:Fin e,(saved.paths.get i).length≤bound)
    (hstrengths : first+pathPrefix saved (pathTrim mediator) e≤J)
    (hterminal : ∀cursor j,(GeometryOutput.terminalCoordinate (packedVector saved) constants cursor j).bits.length≤BG)
    (hmediator : ∀cursor j,(GeometryOutput.mediatorCoordinate (packedVector saved) constants cursor j).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B) (hJ : J.bits.length≤B)
    (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (old inner : List Bool) (hold : BankArray.Word s.val 972 old) (hOld : old.length≤BG)
    (hinner : BankArray.Word s.val 973 inner) (hInner : inner.length≤BG)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t word origin w r inner',Executes input tape (loadedPathsCode mediator) cost s t ∧
      cost≤loadedPathsCost BG B e bound profile template ∧
      GeometryOutput.Context (packedVector saved) base width BG clock constants w t ∧ w 971=packedLength saved ∧
      WellPayload.State strengths P B (first+pathPrefix saved (pathTrim mediator) e) profile template r t ∧
      t.val.output=(pathsStream saved constants mediator P numerators profile template first e).reverse++s.val.output ∧
      t.val.tapes 972=BitTape.shifted word origin ∧ word.length=e.bits.length ∧
      BankArray.Word t.val 973 inner' ∧ inner'.length≤BG := by
  obtain ⟨c0,a,e0,hc0,ga,pa,oa,ka⟩ := cursor_executes g true v hv hthree (originals_span saved) hn
    strengths profile template rv p input tape
  have wa := BankArray.word_of_eq (ka 972 (by decide)) hold
  have ia := BankArray.word_of_eq (ka 973 (by decide)) hinner
  obtain ⟨c1,b,e1,hc1,gb,pb,wb,ob,kb⟩ := loadCounter_executes ga 964 (by decide)
    strengths profile template rv pa old wa hOld input tape
  have ib := BankArray.word_of_eq kb ia
  have heq : Function.update gv 971 (if true then 3*v else 0) 964=e := by
    rw [Function.update_of_ne (by decide : (964:ℕ)≠971),g.fixed 964 (by decide),he]
  rw [heq] at wb
  obtain ⟨origin,wb⟩ := wb
  obtain ⟨c2,t,word,w,r,inner',e2,hc2,gt,ixt,pt,ot,wt,wl,it,il⟩ := paths_executes saved gb
    hw hBG hlen hn hfit hb hwidth ho mediator first bound (by simp) htwo hbound
    hstrengths hterminal hmediator strengths numerators hc P B hm hP hJ profile template rv pb
    inner ib hInner input tape e.bits origin (addressValue_bits e) wb
  have eB : e.bits.length≤BG := by
    have := g.wordWidth 964 (by decide)
    rw [g.fixed 964 (by decide),he] at this
    exact this
  refine ⟨c0+(c1+c2),t,word,origin,w,r,inner',e0.seq (e1.seq e2),?_,gt,ixt,pt,?_,wt,wl,it,il⟩
  · have hc2' := hc2.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left (e+1) (show 13*e.bits.length+15≤13*BG+15 by omega)) _)
    unfold loadedPathsCost
    omega
  · exact ot.trans (by rw [ob,oa])

#print axioms loadedPaths_executes
end Maxwell.Continuum.WellOutput
