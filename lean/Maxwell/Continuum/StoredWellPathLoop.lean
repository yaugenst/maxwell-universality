import Maxwell.Continuum.StoredWellPath
import Maxwell.Continuum.SourceGeometryPathCounts

/-! The outer pass consumes the stored paths in their arithmetic order.
The number of records and every address follow from the literal packing. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
open Maxwell.Logical.Routing Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def pathLength {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : ℕ) : ℕ :=
  if hi:i<e then (saved.paths.get ⟨i,hi⟩).length else 0

def pathChunk {v e : ℕ} (saved : SourceEmission.Geometry v e) (constants : ℕ→ℕ) (mediator : Bool)
    (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) (first i : ℕ) : List Bool :=
  pathStream (packedVector saved) constants mediator P numerators profile template
    (pathOffset saved i) (first+pathPrefix saved (pathTrim mediator) i) (pathLength saved i)

def pathsStream {v e : ℕ} (saved : SourceEmission.Geometry v e) (constants : ℕ→ℕ) (mediator : Bool)
    (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) (first count : ℕ) : List Bool :=
  (List.range count).flatMap (pathChunk saved constants mediator P numerators profile template first)

theorem pathsStream_succ {v e : ℕ} (saved : SourceEmission.Geometry v e) (constants : ℕ→ℕ)
    (mediator : Bool) (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) (first count : ℕ) :
    pathsStream saved constants mediator P numerators profile template first (count+1)=
      pathsStream saved constants mediator P numerators profile template first count++
        pathChunk saved constants mediator P numerators profile template first count := by
  simp [pathsStream,List.range_succ]

def pathsCode (mediator : Bool) : Code := countedProgram 972 (pathCode mediator)

theorem paths_executes {v e base width BG J : ℕ} (saved : SourceEmission.Geometry v e)
    {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context (packedVector saved) base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : (packedLength saved).bits.length≤BG)
    (hfit : ∀i,((packedVector saved).get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (mediator : Bool) (first bound : ℕ) (hstart : gv 971=3*v)
    (htwo : ∀i:Fin e,2≤(saved.paths.get i).length) (hbound : ∀i:Fin e,(saved.paths.get i).length≤bound)
    (hstrengths : first+pathPrefix saved (pathTrim mediator) e≤J)
    (hterminal : ∀cursor j,(GeometryOutput.terminalCoordinate (packedVector saved) constants cursor j).bits.length≤BG)
    (hmediator : ∀cursor j,(GeometryOutput.mediatorCoordinate (packedVector saved) constants cursor j).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B) (hJ : J.bits.length≤B)
    (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (old : List Bool) (hold : BankArray.Word s.val 973 old) (hOld : old.length≤BG)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hx : addressValue xs=e) (hword : s.val.tapes 972=BitTape.shifted xs origin) :
    ∃cost t word w r inner,Executes input tape (pathsCode mediator) cost s t ∧
      cost≤(e+1)*(13*xs.length+15)+e*pathCost BG B bound profile template ∧
      GeometryOutput.Context (packedVector saved) base width BG clock constants w t ∧ w 971=packedLength saved ∧
      WellPayload.State strengths P B (first+pathPrefix saved (pathTrim mediator) e) profile template r t ∧
      t.val.output=(pathsStream saved constants mediator P numerators profile template first e).reverse++s.val.output ∧
      t.val.tapes 972=BitTape.shifted word origin ∧ word.length=xs.length ∧
      BankArray.Word t.val 973 inner ∧ inner.length≤BG := by
  let inv : ℕ→Store→Prop := fun remaining t=>remaining≤e ∧ ∃w r inner,
    GeometryOutput.Context (packedVector saved) base width BG clock constants w t ∧
    w 971=pathOffset saved (e-remaining) ∧
    WellPayload.State strengths P B (first+pathPrefix saved (pathTrim mediator) (e-remaining)) profile template r t ∧
    t.val.output=(pathsStream saved constants mediator P numerators profile template first (e-remaining)).reverse++s.val.output ∧
    BankArray.Word t.val 973 inner ∧ inner.length≤BG
  have stable : ∀q a b,CountedShifted.Frame 972 a b→inv q a→inv q b := by
    intro q a b f h
    obtain ⟨w,r,inner,ga,ix,pa,out,wi,li⟩ := h.2
    have gb := ga.count_frame 972 (by decide) f
    have pb := pa.geometry_frame gb.ready f.2.2.1 (fun k _ hr=>f.2.2.2.2.2.1 k (by omega))
    exact ⟨h.1,w,r,inner,gb,ix,pb,f.2.2.2.2.1.trans out,
      BankArray.word_of_eq (f.2.2.2.2.2.1 973 (by decide)) wi,li⟩
  have step : ∀q ys a,inv (q+1) a→a.val.tapes 972=BitTape.shifted ys origin→
      addressValue ys=q→ys.length=xs.length→
      ∃c b,Executes input tape (pathCode mediator) c a b ∧ inv q b ∧
        b.val.tapes 972=BitTape.shifted ys origin ∧ c≤pathCost BG B bound profile template := by
    intro q ys a hh word _ _
    obtain ⟨w,r,inner,ga,ix,pa,out,wi,li⟩ := hh.2
    let i : Fin e := ⟨e-(q+1),by have := hh.1;omega⟩
    have he : i.val+1=e-q := by have := hh.1;dsimp [i];omega
    have hsi : first+pathPrefix saved (pathTrim mediator) i.val+
        ((saved.paths.get i).length-pathTrim mediator)≤J := by
      rw [Nat.add_assoc,←pathPrefix_succ saved (pathTrim mediator) i]
      exact (Nat.add_le_add_left (pathPrefix_le_end saved (pathTrim mediator) (i.val+1)) first).trans hstrengths
    obtain ⟨c,b,word1,origin1,w1,r1,ex,hcst,gb,ib,pb,ob,wb,wl,kb⟩ :=
      path_executes ga hw hBG hlen hn hfit hb hwidth ho mediator
        (pathOffset saved i.val) (saved.paths.get i).length (first+pathPrefix saved (pathTrim mediator) i.val)
        ix (pathOffset_span saved i) (path_length_lookup saved i) (htwo i) hsi hterminal hmediator
        strengths numerators hc P B hm hP hJ profile template r pa inner wi li input tape
    have ilen : (saved.paths.get i).length.bits.length≤BG := by
      rw [←path_length_lookup saved i]
      exact (GeometryOutput.arrayValue_bits (packedVector saved) width hfit (pathOffset saved i.val)).trans hBG
    refine ⟨c,b,ex,⟨by omega,w1,r1,word1,gb,?_,?_,?_,⟨origin1,wb⟩,wl.trans_le ilen⟩,
      kb.trans word,hcst.trans (pathCost_mono BG B _ bound (hbound i) profile template)⟩
    · rw [ib,←pathOffset_succ saved i,he]
    · rw [←he,pathPrefix_succ saved (pathTrim mediator) i]
      simpa only [Nat.add_assoc] using pb
    · rw [ob,out,←he,pathsStream_succ]
      have hc' : pathChunk saved constants mediator P numerators profile template first i.val=
          pathStream (packedVector saved) constants mediator P numerators profile template
            (pathOffset saved i.val) (first+pathPrefix saved (pathTrim mediator) i.val) (saved.paths.get i).length := by
        simp only [pathChunk,pathLength,dite_eq_left i.isLt]
      rw [hc']
      simp only [List.reverse_append,List.append_assoc]
      rfl
  have initial : inv e s := by
    refine ⟨le_rfl,gv,rv,old,g,?_,?_,?_,hold,hOld⟩
    · simpa only [Nat.sub_self,pathOffset_zero] using hstart
    · simpa only [Nat.sub_self,pathPrefix_zero,Nat.add_zero] using p
    · simp only [Nat.sub_self,pathsStream,List.range_zero,List.flatMap_nil,List.reverse_nil,List.nil_append]
  obtain ⟨cost,t,word,ex,hfinal,wt,wl,_,cb⟩ := counted_executes_sized 972 origin (pathCode mediator)
    input tape xs.length inv (fun _=>pathCost BG B bound profile template) stable step e xs s hx hword rfl initial
  obtain ⟨w,r,inner,gt,ix,pt,out,wi,li⟩ := hfinal.2
  refine ⟨cost,t,word,w,r,inner,ex,?_,gt,?_,?_,?_,wt,wl,wi,li⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using cb
  · simpa only [Nat.sub_zero,pathOffset_end] using ix
  · simpa only [Nat.sub_zero] using pt
  · simpa only [Nat.sub_zero] using out

#print axioms paths_executes
end Maxwell.Continuum.WellOutput
