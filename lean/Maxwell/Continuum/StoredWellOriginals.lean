import Maxwell.Continuum.StoredWellControl
import Maxwell.Continuum.StoredWellPathLoop

/-! The original-well pass initializes its own cursor and stored counter. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def originalCode : Code := .seq (cursorCode false)
  (.seq (WordReplace.code 963 972) (terminalLoopCode 972))

def originalCost (BG B vertices : ℕ) (profile template : List Bool) : ℕ :=
  2^23*(BG+3)^2+(21*BG+21)+(vertices+1)*(13*BG+15)+vertices*stepCost BG B profile template

theorem original_executes {v e base width BG J : ℕ} (saved : SourceEmission.Geometry v e)
    {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context (packedVector saved) base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : (packedLength saved).bits.length≤BG)
    (hfit : ∀i,((packedVector saved).get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (hv : constants 963=v) (hthree : constants 969=3) (first : ℕ) (hstrengths : first+v≤J)
    (hterminal : ∀cursor j,(GeometryOutput.terminalCoordinate (packedVector saved) constants cursor j).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B) (hJ : J.bits.length≤B)
    (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (old : List Bool) (hold : BankArray.Word s.val 972 old) (hOld : old.length≤BG)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t word origin w r,Executes input tape originalCode cost s t ∧
      cost≤originalCost BG B v profile template ∧
      GeometryOutput.Context (packedVector saved) base width BG clock constants w t ∧ w 971=3*v ∧
      WellPayload.State strengths P B (first+v) profile template r t ∧
      t.val.output=(terminalStream (packedVector saved) constants P numerators profile template 0 first v).reverse++s.val.output ∧
      t.val.tapes 972=BitTape.shifted word origin ∧ word.length=v.bits.length ∧
      t.val.tapes 973=s.val.tapes 973 := by
  obtain ⟨c0,a,e0,hc0,ga,pa,oa,ka⟩ := cursor_executes g false v hv hthree (originals_span saved) hn
    strengths profile template rv p input tape
  have wa := BankArray.word_of_eq (ka 972 (by decide)) hold
  obtain ⟨c1,b,e1,hc1,gb,pb,wb,ob,kb⟩ := loadCounter_executes ga 963 (by decide)
    strengths profile template rv pa old wa hOld input tape
  have heq : Function.update gv 971 (if false then 3*v else 0) 963=v := by
    rw [Function.update_of_ne (by decide : (963:ℕ)≠971),g.fixed 963 (by decide),hv]
  rw [heq] at wb
  obtain ⟨origin,wb⟩ := wb
  obtain ⟨c2,t,word,w,r,e2,hc2,gt,ixt,pt,ot,wt,wl,kt⟩ := terminalLoop_executes gb
    hw hBG hlen hn hfit hb hwidth ho 0 v first 972 (by decide) (by simp) (by simpa using originals_span saved)
    hstrengths (fun _ _=>hterminal _) strengths numerators hc P B hm hP hJ profile template rv pb
    input tape v.bits origin (addressValue_bits v) wb
  have vB : v.bits.length≤BG := by
    have := g.wordWidth 963 (by decide)
    rw [g.fixed 963 (by decide),hv] at this
    exact this
  refine ⟨c0+(c1+c2),t,word,origin,w,r,e0.seq (e1.seq e2),?_,gt,?_,pt,?_,wt,wl,?_⟩
  · have hc2' := hc2.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left (v+1) (show 13*v.bits.length+15≤13*BG+15 by omega)) _)
    unfold originalCost
    omega
  · simpa only [Nat.zero_add] using ixt
  · exact ot.trans (by rw [ob,oa])
  · exact (kt 973 (by decide) (by decide)).trans (kb.trans (ka 973 (by decide)))

#print axioms original_executes
end Maxwell.Continuum.WellOutput
