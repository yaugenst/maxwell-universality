import Maxwell.Continuum.StoredWellBody

/-! One fixed Boolean program serializes the entire stored well family.
Its list count is the count computed by the geometry producer on tape988. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def code : Code := .seq (EmitNatural.code 988) bodyCode

def bits {v e : ℕ} (saved : SourceEmission.Geometry v e) (constants : ℕ→ℕ)
    (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) : List Bool :=
  Codec.nat (siteCount saved)++bodyBits saved constants P numerators profile template

def costBound (BG B vertices edges bound : ℕ) (profile template : List Bool) : ℕ :=
  20*BG+24+originalCost BG B vertices profile template+2*loadedPathsCost BG B edges bound profile template

theorem executes {v e base width BG : ℕ} (saved : SourceEmission.Geometry v e)
    {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context (packedVector saved) base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : (packedLength saved).bits.length≤BG)
    (hfit : ∀i,((packedVector saved).get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (hv : constants 963=v) (he : constants 964=e) (hthree : constants 969=3)
    (hcount : gv 988=siteCount saved)
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
    ∃cost t word origin w r inner',Executes input tape code cost s t ∧
      cost≤costBound BG B v e bound profile template ∧
      GeometryOutput.Context (packedVector saved) base width BG clock constants w t ∧ w 971=packedLength saved ∧
      WellPayload.State strengths P B (siteCount saved) profile template r t ∧
      t.val.output=(bits saved constants P numerators profile template).reverse++s.val.output ∧
      t.val.tapes 972=BitTape.shifted word origin ∧ word.length=e.bits.length ∧
      BankArray.Word t.val 973 inner' ∧ inner'.length≤BG := by
  obtain ⟨c0,a,e0,hc0,ga,pa,oa,fa⟩ := header_executes g strengths profile template rv p input tape
  have wa := BankArray.word_of_eq (congrFun fa.2.2.2.2 972) hold
  have ia := BankArray.word_of_eq (congrFun fa.2.2.2.2 973) hinner
  obtain ⟨c1,t,word,origin,w,r,inner',e1,hc1,gt,ixt,pt,ot,wt,wl,it,il⟩ := body_executes saved ga
    hw hBG hlen hn hfit hb hwidth ho hv he hthree bound htwo hbound hterminal hmediator
    strengths numerators hc P B hm hP hJ profile template rv pa old inner wa hOld ia hInner input tape
  refine ⟨c0+c1,t,word,origin,w,r,inner',e0.seq e1,?_,gt,ixt,pt,?_,wt,wl,it,il⟩
  · unfold costBound
    omega
  · rw [ot,oa,hcount]
    simp only [bits,List.reverse_append,List.append_assoc]

#print axioms executes
end Maxwell.Continuum.WellOutput
