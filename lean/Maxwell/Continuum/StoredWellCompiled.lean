import Maxwell.Continuum.StoredWellCost

/-! Actual execution of one fixed compiled Boolean serializer, including
all stored geometry reads and all per-record payload copies. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def polynomialCost (BG B vertices edges bound : ℕ) (profile template : List Bool) : ℕ :=
  2^40*(vertices+edges*(bound+1)+1)*workSize BG B profile template

theorem compiled_run {v e base width BG : ℕ} (saved : SourceEmission.Geometry v e)
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
    ∃t word origin w r inner',
      (runPriced (code.compile.next input tape) (polynomialCost BG B v e bound profile template+1) s.val).finished=
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (polynomialCost BG B v e bound profile template+1) s.val).instructions≤
        polynomialCost BG B v e bound profile template ∧
      GeometryOutput.Context (packedVector saved) base width BG clock constants w t ∧ w 971=packedLength saved ∧
      WellPayload.State strengths P B (siteCount saved) profile template r t ∧
      t.val.output=(bits saved constants P numerators profile template).reverse++s.val.output ∧
      t.val.tapes 972=BitTape.shifted word origin ∧ word.length=e.bits.length ∧
      BankArray.Word t.val 973 inner' ∧ inner'.length≤BG := by
  obtain ⟨cost,t,word,origin,w,r,inner',ex,hcost,rest⟩ := executes saved g hw hBG hlen hn hfit hb hwidth ho
    hv he hthree hcount bound htwo hbound hterminal hmediator strengths numerators hc P B hm hP hJ
    profile template rv p old inner hold hOld hinner hInner input tape
  have hpoly := hcost.trans (costBound_polynomial BG B v e bound profile template)
  obtain ⟨run,steps⟩ := ex.compiled_run (polynomialCost BG B v e bound profile template+1) (by
    change cost≤polynomialCost BG B v e bound profile template at hpoly
    omega)
  exact ⟨t,word,origin,w,r,inner',run,steps ▸ hpoly,rest⟩

#print axioms compiled_run
end Maxwell.Continuum.WellOutput
