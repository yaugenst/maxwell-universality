import Maxwell.Continuum.StoredWellGeometryFrame

/-! Literal placement and payload interleaving. Every emitted record
contains its own strength and both common polynomial descriptions. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def stepCost (BG B : ℕ) (profile template : List Bool) : ℕ :=
  2^30*(BG+3)^2+2^25*(B+5)^2+10*(profile.length+template.length)+100

def terminalCode : Code := .seq GeometryOutput.terminalStepCode WellPayload.code
def mediatorCode : Code := .seq GeometryOutput.mediatorStepCode WellPayload.code

theorem terminal_executes {n base width BG J : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : n.bits.length≤BG)
    (hfit : ∀i,(data.get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (hix : gv 971+3≤n)
    (hcoord : ∀j,(GeometryOutput.terminalCoordinate data constants (gv 971) j).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B)
    (profile template : List Bool) (i : Fin J) (hi : i.val.bits.length≤B)
    (rv : ℕ→Parts) (p : WellPayload.State strengths P B i.val profile template rv s)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t w,Executes input tape terminalCode cost s t ∧ cost≤stepCost BG B profile template ∧
      GeometryOutput.Context data base width BG clock constants w t ∧ w 971=gv 971+3 ∧
      WellPayload.State strengths P B (i.val+1) profile template (Function.update rv 0 (strengths.get i)) t ∧
      t.val.output=(GeometryOutput.terminalBits data constants (gv 971)++
        WellPayload.bits P (numerators i.val) profile template).reverse++s.val.output ∧
      (∀k∈({972,973}:Finset ℕ),t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,a,w,e0,hc0,ga,ix,oa,keepa⟩ := GeometryOutput.terminalStep_executes g hw hBG hlen hn hfit hb hwidth ho
    hix hcoord input tape
  have mema := e0.protectsMemory WellPayload.terminalStep_memory
  have pa := p.geometry_frame ga.ready mema (fun k hk hr=>keepa k hk (by
    simp only [Finset.mem_insert,Finset.mem_singleton];omega))
  obtain ⟨c1,t,e1,hc1,pt,ot,memt,keept⟩ := WellPayload.executes strengths numerators hc P B hm hP
    profile template i hi rv input tape a pa
  refine ⟨c0+c1,t,w,e0.seq e1,?_,WellPayload.geometry_context_frame ga pt memt keept,ix,pt,?_,?_⟩
  · unfold stepCost
    omega
  · rw [ot,oa,List.reverse_append,List.append_assoc]
  · intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl
    · exact (keept 972 (by decide) (by decide) (by decide)).trans (keepa 972 (by decide) (by decide))
    · exact (keept 973 (by decide) (by decide) (by decide)).trans (keepa 973 (by decide) (by decide))

theorem mediator_executes {n base width BG J : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width BG clock constants gv s)
    (hw : 0<width) (hBG : width≤BG) (hlen : clock.length=width) (hn : n.bits.length≤BG)
    (hfit : ∀i,(data.get i).bits.length≤width)
    (hb : constants 960=base) (hwidth : constants 961=width) (ho : constants 970=1)
    (cursor : ℕ) (hcursor : gv 971=cursor+3) (hix : cursor+6≤n)
    (hprev : ∀j:Fin 3,gv (976+j.val)=GeometryOutput.arrayValue data (cursor+j.val))
    (hcoord : ∀j,(GeometryOutput.mediatorCoordinate data constants cursor j).bits.length≤BG)
    (strengths : Table J) (numerators : ℕ→ℤ)
    (hc : ∀i:Fin J,strengths.get i=Parts.literal ((numerators i.val:ℤ):ℚ))
    (P B : ℕ) (hm : strengths.MetadataWidth B) (hP : P.bits.length≤B)
    (profile template : List Bool) (i : Fin J) (hi : i.val.bits.length≤B)
    (rv : ℕ→Parts) (p : WellPayload.State strengths P B i.val profile template rv s)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t w,Executes input tape mediatorCode cost s t ∧ cost≤stepCost BG B profile template ∧
      GeometryOutput.Context data base width BG clock constants w t ∧ w 971=cursor+6 ∧
      (∀j:Fin 3,w (976+j.val)=GeometryOutput.arrayValue data (cursor+3+j.val)) ∧
      WellPayload.State strengths P B (i.val+1) profile template (Function.update rv 0 (strengths.get i)) t ∧
      t.val.output=(GeometryOutput.mediatorBits data constants cursor++
        WellPayload.bits P (numerators i.val) profile template).reverse++s.val.output ∧
      (∀k∈({972,973}:Finset ℕ),t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,a,w,e0,hc0,ga,ix,prev,oa,keepa⟩ := GeometryOutput.mediatorStep_executes g hw hBG hlen hn hfit hb hwidth ho
    cursor hcursor hix hprev hcoord input tape
  have mema := e0.protectsMemory WellPayload.mediatorStep_memory
  have pa := p.geometry_frame ga.ready mema (fun k hk hr=>keepa k hk (by
    simp only [Finset.mem_insert,Finset.mem_singleton];omega))
  obtain ⟨c1,t,e1,hc1,pt,ot,memt,keept⟩ := WellPayload.executes strengths numerators hc P B hm hP
    profile template i hi rv input tape a pa
  refine ⟨c0+c1,t,w,e0.seq e1,?_,WellPayload.geometry_context_frame ga pt memt keept,ix,prev,pt,?_,?_⟩
  · unfold stepCost
    omega
  · rw [ot,oa,List.reverse_append,List.append_assoc]
  · intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl
    · exact (keept 972 (by decide) (by decide) (by decide)).trans (keepa 972 (by decide) (by decide))
    · exact (keept 973 (by decide) (by decide) (by decide)).trans (keepa 973 (by decide) (by decide))

#print axioms terminal_executes
#print axioms mediator_executes
end Maxwell.Continuum.WellOutput
