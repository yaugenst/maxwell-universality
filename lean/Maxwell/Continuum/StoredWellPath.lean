import Maxwell.Continuum.StoredWellMediatorPath

/-! A common concrete contract for the two fixed chronological path passes. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def pathTrim (mediator : Bool) : ℕ := if mediator then 1 else 2

def pathCode (mediator : Bool) : Code := if mediator then mediatorPathCode else internalPathCode

def pathStream {n : ℕ} (data : Vector ℕ n) (constants : ℕ→ℕ) (mediator : Bool)
    (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool) (start first count : ℕ) : List Bool :=
  if mediator then mediatorStream data constants P numerators profile template (start+1) first (count-1)
  else terminalStream data constants P numerators profile template (start+4) first (count-2)

theorem path_executes {n base width BG J : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : n.bits.length≤BG)
    (hfit : ∀i,(data.get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (mediator : Bool) (start count first : ℕ) (hstart : gv 971=start) (hspan : start+1+3*count≤n)
    (hcount : GeometryOutput.arrayValue data start=count) (htwo : 2≤count)
    (hstrengths : first+(count-pathTrim mediator)≤J)
    (hterminal : ∀cursor j,(GeometryOutput.terminalCoordinate data constants cursor j).bits.length≤BG)
    (hmediator : ∀cursor j,(GeometryOutput.mediatorCoordinate data constants cursor j).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B) (hJ : J.bits.length≤B)
    (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (old : List Bool) (hold : BankArray.Word s.val 973 old) (hOld : old.length≤BG)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t word origin w r,Executes input tape (pathCode mediator) cost s t ∧
      cost≤pathCost BG B count profile template ∧
      GeometryOutput.Context data base width BG clock constants w t ∧ w 971=start+1+3*count ∧
      WellPayload.State strengths P B (first+(count-pathTrim mediator)) profile template r t ∧
      t.val.output=(pathStream data constants mediator P numerators profile template start first count).reverse++s.val.output ∧
      t.val.tapes 973=BitTape.shifted word origin ∧ word.length=count.bits.length ∧
      t.val.tapes 972=s.val.tapes 972 := by
  cases mediator with
  | false =>
    exact internalPath_executes g hw hBG hlen hn hfit hb hwidth ho start count first hstart
      hspan hcount htwo hstrengths (fun _ _=>hterminal _) strengths numerators hc P B hm hP hJ
      profile template rv p old hold hOld input tape
  | true =>
    exact mediatorPath_executes g hw hBG hlen hn hfit hb hwidth ho start count first hstart
      hspan hcount htwo hstrengths (fun _ _=>hmediator _) strengths numerators hc P B hm hP hJ
      profile template rv p old hold hOld input tape

theorem pathCost_mono (BG B count bound : ℕ) (h : count≤bound) (profile template : List Bool) :
    pathCost BG B count profile template≤pathCost BG B bound profile template := by
  unfold pathCost
  exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.add_le_add_right h 1)) _)
    (Nat.mul_le_mul_right _ h)

#print axioms path_executes
end Maxwell.Continuum.WellOutput
