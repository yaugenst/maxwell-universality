import Maxwell.Continuum.StoredWellMediatorLoop

/-! The path header is read from the packed geometry itself. Installing
its inner loop counter preserves the actual strength and payload caches. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem pathSetup_executes {n base width BG J P B first : ℕ} {data : Vector ℕ n}
    {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : n.bits.length≤BG)
    (hfit : ∀i,(data.get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (start count trim : ℕ) (hstart : gv 971=start) (hspan : start+4≤n)
    (hcount : GeometryOutput.arrayValue data start=count) (htrim : trim≤count) (htrim2 : trim≤2)
    (strengths : Table J) (profile template : List Bool) (rv : ℕ→Parts)
    (p : WellPayload.State strengths P B first profile template rv s)
    (old : List Bool) (hold : BankArray.Word s.val 973 old) (hOld : old.length≤BG)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t word origin w,Executes input tape (GeometryOutput.pathSetupCode trim) cost s t ∧
      cost≤2^26*(BG+3)^2 ∧
      GeometryOutput.Context data base width BG clock constants w t ∧ w 971=start+4 ∧
      (∀j:Fin 3,w (976+j.val)=GeometryOutput.arrayValue data (start+1+j.val)) ∧
      WellPayload.State strengths P B first profile template rv t ∧
      t.val.tapes 973=BitTape.shifted word origin ∧ word.length=count.bits.length ∧
      addressValue word=count-trim ∧ t.val.output=s.val.output ∧ t.val.tapes 972=s.val.tapes 972 := by
  obtain ⟨cost,t,word,origin,w,ex,hc,gt,ix,prev,wt,wl,wv,out,keep⟩ :=
    GeometryOutput.pathSetup_executes g hw hBG hlen hn hfit hb hwidth ho
      start count trim hstart hspan hcount htrim htrim2 old hold hOld input tape
  have pt := p.geometry_frame gt.ready (ex.protectsMemory (WellPayload.pathSetup_memory trim))
    (fun k hk hr=>keep k hk (by simp only [Finset.mem_insert,Finset.mem_singleton];omega))
  exact ⟨cost,t,word,origin,w,ex,hc,gt,ix,prev,pt,wt,wl,wv,out,
    keep 972 (by decide) (by decide)⟩

#print axioms pathSetup_executes
end Maxwell.Continuum.WellOutput
