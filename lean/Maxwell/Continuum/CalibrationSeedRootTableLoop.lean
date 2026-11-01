import Maxwell.Continuum.CalibrationSeedRootTableStep
import Maxwell.Continuum.RationalDataflowSizedCounted

/-! Actual fixed-code traversal of every seed alias row. The loop count is
a stored word, and every normalized index, cache lookup and output write is charged. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def tableCode : Code := countedProgram 801 tableBodyCode
def tableCost (M D B length : ℕ) : ℕ :=
  (ArrayDecodeMachine.aliasRowCount (3*M+D)+1)*(13*length+15)+
    ArrayDecodeMachine.aliasRowCount (3*M+D)*tableBodyCost B

theorem table_executes (M D B : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (v : ℕ→Parts) (hB : 2≤B) (width : WidthBank slots B (resetParts v))
    (good : Good slots (resetParts v)) (metadata : a.MetadataWidth B)
    (entryWidth : ∀i,(a.get i).Width B) (entryValid : ∀i,(a.get i).Valid)
    (xs : List Bool) (origin : ℤ) (value : addressValue xs=ArrayDecodeMachine.aliasRowCount (3*M+D))
    (length : xs.length≤B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (initial : TableState M D B a v (ArrayDecodeMachine.aliasRowCount (3*M+D)) s)
    (counter : s.val.tapes 801=BitTape.shifted xs origin) :
    ∃cost t finalWord,Executes input tape tableCode cost s t ∧ cost≤tableCost M D B xs.length ∧
      Nonempty (TableState M D B a v 0 t) ∧ t.val.tapes 801=BitTape.shifted finalWord origin ∧
      finalWord.length=xs.length ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output := by
  let inv : ℕ→Store→Prop := fun r st=>Nonempty (TableState M D B a v r st) ∧
    st.val.inputHead=s.val.inputHead ∧ st.val.randomCursor=s.val.randomCursor ∧ st.val.output=s.val.output
  have stable : ∀r st out,CountedShifted.Frame 801 st out→inv r st→inv r out := by
    intro r st out f hh
    rcases hh.1 with ⟨state⟩
    exact ⟨⟨state.count_frame f⟩,f.2.1.trans hh.2.1,f.2.2.2.1.trans hh.2.2.1,f.2.2.2.2.1.trans hh.2.2.2⟩
  have step : ∀r ys st,inv (r+1) st→st.val.tapes 801=BitTape.shifted ys origin→
      addressValue ys=r→ys.length=xs.length→
      ∃cost out,Executes input tape tableBodyCode cost st out ∧ inv r out ∧
        out.val.tapes 801=BitTape.shifted ys origin ∧ cost≤tableBodyCost B := by
    intro r ys st hh hw hv hl
    rcases hh.1 with ⟨state⟩
    obtain ⟨cost,out,e,hc,ht,word,inp,rnd,output⟩ := state.step_executes hB width good metadata
      entryWidth entryValid ys hv (by omega) input tape ⟨origin,hw⟩
    exact ⟨cost,out,e,⟨ht,inp.trans hh.2.1,rnd.trans hh.2.2.1,output.trans hh.2.2.2⟩,word.trans hw,hc⟩
  obtain ⟨cost,t,finalWord,e,ht,word,hlen,_,hc⟩ := counted_executes_sized 801 origin tableBodyCode
    input tape xs.length inv (fun _=>tableBodyCost B) stable step
    (ArrayDecodeMachine.aliasRowCount (3*M+D)) xs s value counter rfl ⟨⟨initial⟩,rfl,rfl,rfl⟩
  refine ⟨cost,t,finalWord,e,?_,ht.1,word,hlen,ht.2.1,ht.2.2.1,ht.2.2.2⟩
  simpa only [tableCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hc

#print axioms table_executes
end Maxwell.Continuum.Calibration.SeedRoot
