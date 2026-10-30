import Maxwell.Continuum.CutoffMonomialAccumulator
import Maxwell.Continuum.RationalDataflowRowWritePlan
import Maxwell.Continuum.RationalDataflowArrayMap

/-! The literal cached Chebyshev row update: four indexed reads, four
arithmetic operations, and three indexed writes. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def monomialReadPlan : List (ℕ×ℕ) := [(4,0),(5,1),(1,2),(6,3)]
def monomialWritePlan : List (ℕ×ℕ) := [(4,1),(5,6),(6,7)]

def monomialRowCode : Code := .seq (rowPlanCode 4 monomialReadPlan)
  (.seq monomialRowControl.code (rowWritePlanCode 4 monomialWritePlan))

def monomialLoaded {n : ℕ} (a : Table n) (row : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  rowPlanValues a 4 row monomialReadPlan v

def monomialRowState {n : ℕ} (a : Table n) (row : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  monomialRowControl.evaluate (monomialLoaded a row v)

def monomialRowTable {n m : ℕ} (a : Table n) (b : Table m) (row : ℕ) (v : ℕ→Parts) : Table m :=
  rowWriteTable 4 row monomialWritePlan (monomialRowState a row v) b

theorem monomialRow_executes {D : ℕ} (a b : Table (4*(D+1))) (W : ℕ)
    (haMeta : a.MetadataWidth W) (hbMeta : b.MetadataWidth W)
    (hpositive : 0<addressValue b.width) (hslot : W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b) (v : ℕ→Parts)
    (hv : WidthBank (Finset.range 8) W v) (row : ℕ) (hr : row<D)
    (htrace : monomialRowControl.WidthTrace (Finset.range 8) W (monomialLoaded a row v))
    (hgood : Good (Finset.range 8) (monomialLoaded a row v))
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length≤W)
    (hrow : addressValue word=row) (s : Store) (hs : RationalDataflow.Ready (Finset.range 8) v s)
    (ha : a.Ready s) (hb : b.OutputReady s) (hi : BankArray.Word s.val 201 word)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t, Executes input tape monomialRowCode cost s t ∧
      cost≤2^112*(W+16)^2 ∧ RationalDataflow.Ready (Finset.range 8) (monomialRowState a row v) t ∧
      a.Ready t ∧ (monomialRowTable a b row v).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      (∀i,200 ≤ i → i<220 → t.val.tapes i=s.val.tapes i) := by
  have readValid : ∀x∈monomialReadPlan,x.2∈Finset.range 8 := by
    simp [monomialReadPlan]
  have readOffsets : ∀x∈monomialReadPlan,x.1.bits.length≤3 := by decide
  have readIndices : ∀x∈monomialReadPlan,4*addressValue word+x.1<4*(D+1) := by
    intro x hx
    simp only [monomialReadPlan,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp only [hrow] <;> omega
  obtain ⟨cr,r,er,hcr,br,_,ar,zr,fr⟩ := rowPlan_executes a (Finset.range 8) 4 3 W monomialReadPlan
    readValid readOffsets haMeta v hv input tape word hlen readIndices s hs ha hi hblank
  have br' : RationalDataflow.Ready (Finset.range 8) (monomialLoaded a row v) r := by
    simpa only [hrow,monomialLoaded] using br
  have bor := hb.rowPlan_frame fr ar.scratch ar.seven
  obtain ⟨cc,p,ec,hcc,bp,fp⟩ := monomialRowControl.executes (Finset.range 8)
    monomialRowControl_valid _ W htrace hgood (monomialRowControl_admissible _) input tape r br'
  have ap := ar.arithmetic_frame (Finset.range 8) fp bp.2
  have bop := bor.shared_frame (Finset.range 8) (fp.mono (workspace_subset_shared _)) ap.scratch ap.seven
  have zp : ∀i∈RowIndex.ids,RationalAccumulator.Blank p.val i := by
    intro i hi'
    apply RationalAccumulator.blank_of_eq (fp.tapes i _) (zr i hi')
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl | rfl <;> exact outside_workspace _ _ (by decide)
  have ip : BankArray.Word p.val 201 word :=
    BankArray.word_of_eq (fp.tapes 201 (outside_workspace _ _ (by decide)))
      (BankArray.word_of_eq fr.counter hi)
  have writeValid : ∀x∈monomialWritePlan,x.2∈Finset.range 8 := by simp [monomialWritePlan]
  have writeOffsets : ∀x∈monomialWritePlan,x.1.bits.length≤3 := by decide
  have writeIndices : ∀x∈monomialWritePlan,4*addressValue word+x.1<4*(D+1) := by
    intro x hx
    simp only [monomialWritePlan,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp only [hrow] <;> omega
  have fit : ∀x∈monomialWritePlan,((monomialRowState a row v) x.2).Width (addressValue b.width) := by
    intro x hx
    exact (htrace.result x.2 (writeValid x hx)).mono hslot
  obtain ⟨cw,t,ew,hcw,bt,at',bot,zt,ft⟩ := rowWritePlan_executes a b (Finset.range 8) 4 3 W
    monomialWritePlan writeValid writeOffsets hbMeta (monomialRowState a row v) fit
    hpositive hsep hdisjoint input tape word hlen writeIndices p bp ap bop ip zp
  refine ⟨cr+(cc+cw),t,er.seq (ec.seq ew),?_,bt,at',?_,zt,?_⟩
  · have hsteps : monomialRowControl.steps=4 := rfl
    simp only [rowPlanCost,monomialReadPlan,monomialWritePlan,List.length_cons,List.length_nil,
      hsteps] at hcr hcw hcc
    have hbits : (4:ℕ).bits.length=3 := by decide
    simp only [hbits] at hcr hcw
    unfold operationCost at hcc
    nlinarith only [hcr,hcw,hcc,Nat.zero_le W]
  · simpa only [hrow,monomialRowTable] using bot
  · intro i hil hiu
    have hout : i∉workspace (Finset.range 8) := outside_workspace _ i (by omega)
    have hport : i∉ports (Finset.range 8) := fun hm =>
      hout (Finset.mem_union_right _ (Finset.mem_union_left _ hm))
    have hrowout : i∉RowIndex.ids := by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton,not_or]
      omega
    exact (ft.tapes i (by omega) (by omega) hrowout).trans
      ((fp.tapes i hout).trans (fr.tapes i (by omega) hport hrowout))

#print axioms monomialRow_executes
end Maxwell.Continuum.Calibration.RawCutoff
