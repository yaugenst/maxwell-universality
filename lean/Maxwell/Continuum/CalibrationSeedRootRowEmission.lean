import Maxwell.Continuum.CalibrationSeedRootRowStable

/-! Decode one stored alias row, restore the uniform workspace bound, then
execute all six fixed output producers into the canonical coefficient table. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def rowEmissionCode : Code := .seq rowCode (.seq resetCode (phasesCode phases))
def rowEmissionCost (B : ℕ) : ℕ := rowCost B+resetCost (rowWidth B)+(6*producerCost B+1)
def emittedRow (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (v : ℕ→Parts)
    (b : PartArray.Table (2*aliasArraySize (3*M+D))) : PartArray.Table (2*aliasArraySize (3*M+D)) :=
  phasesTable M D a row (decodedCoordinates (3*M+D) (3*row.val)) v phases b

theorem rowEmission_executes (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (b : PartArray.Table (2*aliasArraySize (3*M+D)))
    (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D)))
    (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ) (hB : 2≤B)
    (hM : n 750=M) (hD : n 751=D) (hrow : n 780=row.val)
    (dimension : n 785=aliasArraySize (3*M+D)) (side : n 786=aliasSide (3*M+D))
    (naturalWidth : ∀i∈rowIds,(n i).bits.length≤B)
    (width : WidthBank slots B (resetParts v)) (good : Good slots (resetParts v))
    (metadata : a.MetadataWidth B) (entryWidth : ∀i,(a.get i).Width B)
    (entryValid : ∀i,(a.get i).Valid) (outputMeta : b.MetadataWidth (producerWidth B))
    (positive : 0<addressValue b.width) (fits : producerWidth B≤addressValue b.width)
    (separated : b.Separated) (disjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (natural : NatAssign.Bank rowIds n s.val) (ready : Ready slots (resetParts v) s)
    (four : RationalAccumulator.Blank s.val 4) (cache : a.Ready s) (output : b.OutputReady s) :
    ∃cost t w,Executes input tape rowEmissionCode cost s t ∧ cost≤rowEmissionCost B ∧
      NatAssign.Bank rowIds w t.val ∧ (∀i∈rowIds,(w i).bits.length≤B) ∧
      (∀i∈rowRetained,w i=n i) ∧ Ready slots (resetParts v) t ∧
      RationalAccumulator.Blank t.val 4 ∧ a.Ready t ∧ (emittedRow M D a row v b).OutputReady t ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧
      (∀i,10 ≤ i→i∉producerChanged→t.val.tapes i=s.val.tapes i) ∧
      (∀p∈phases,(entryParts M D a (decodedCoordinates (3*M+D) (3*row.val)) p.1 p.2 v).Valid ∧
        (entryParts M D a (decodedCoordinates (3*M+D) (3*row.val)) p.1 p.2 v).Width (producerWidth B)) := by
  have scratch (i : ℕ) (hi : i<5) : RationalAccumulator.Blank s.val i := by
    by_cases hs : i<4
    · exact ready.2 i hs
    · have he : i=4 := by omega
      simpa only [he] using four
  obtain ⟨c0,u,e0,h0,nu,zu,nwu,f0⟩ := row_executes n B naturalWidth input tape s natural scratch
  have ru := ready_after_row_execution natural ready nu (fun i hi=>zu i (by omega)) f0
  have arrays0 := arrays_after_reset cache output (f0.mono Finset.subset_union_left) ru.2
  obtain ⟨c1,z,e1,h1,nz,nwz,rz,_,_,f1,four1⟩ := reset_executes (rowValues n) (resetParts v)
    (rowWidth B) B (by omega) (rowWidth_ge B) nwu (width.mono (rowWidth_ge B)) good
    (rowValues_fixed_width M D row n B hM hD hrow side naturalWidth)
    (fun i hi _=>width i hi) input tape u nu ru
  rw [resetParts_idempotent] at rz
  have arrays1 := arrays_after_reset arrays0.1 arrays0.2 f1 rz.2
  let nd := resetNumbers (rowValues n)
  have kept (i : ℕ) (hi : i∈rowRetained) : nd i=n i :=
    (resetNumbers_keep (rowValues n) i ((by decide : rowRetained⊆fixedFields) hi)).trans
      (rowValues_retained n i hi)
  have half : nd 752=nd 750/2 := by
    dsimp only [nd]
    rw [resetNumbers_keep _ 752 (by decide),resetNumbers_keep _ 750 (by decide),rowValues_half,
      rowValues_retained n 750 (by decide)]
  have co : coordinates nd=decodedCoordinates (3*M+D) (3*row.val) := by
    rw [resetNumbers_coordinates,rowValues_coordinates,hM,hD,hrow]
  obtain ⟨c2,t,w,e2,h2,nt,nwt,keep,rt,ta,tb,inp,rnd,out,four2,tapes,entries⟩ := phases_executes M D a b
    row phases nd v B hB ((kept 750 (by decide)).trans hM) ((kept 751 (by decide)).trans hD)
    half ((kept 780 (by decide)).trans hrow) ((kept 785 (by decide)).trans dimension) nwz width good
    metadata entryWidth entryValid outputMeta positive fits separated disjoint input tape z nz rz arrays1.1 arrays1.2
  refine ⟨c0+(c1+c2),t,w,e0.seq (e1.seq e2),?_,nt,nwt,
    fun i hi=>(keep i ((by decide : rowRetained⊆fixedFields) hi)).trans (kept i hi),rt,
    RationalAccumulator.blank_of_eq (four2.trans four1) (zu 4 (by decide)),ta,?_,
    inp.trans (f1.inputHead.trans f0.inputHead),rnd.trans (f1.randomCursor.trans f0.randomCursor),
    out.trans (f1.output.trans f0.output),?_,?_⟩
  · change c2≤6*producerCost B+1 at h2
    unfold rowEmissionCost
    omega
  · simpa only [emittedRow,co] using tb
  · intro i hi ho
    have hr : i∉rowWorkspace∪RationalDataflow.workspace slots := fun hh=>ho (Finset.mem_union_left _ hh)
    have hrow : i∉rowWorkspace := fun hh=>hr (Finset.mem_union_left _ hh)
    exact (tapes i hi ho).trans ((f1.tapes i hr).trans (f0.tapes i hrow))
  · simpa only [co] using entries

#print axioms rowEmission_executes
end Maxwell.Continuum.Calibration.SeedRoot
