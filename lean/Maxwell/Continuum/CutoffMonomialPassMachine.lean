import Maxwell.Continuum.CutoffMonomialStateBounds

/-! One complete runtime traversal constructs the next cached Chebyshev
rows and weighted accumulator. Its raw-width traces are proved internally. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def monomialPassTable {D : ℕ} (a b : Table (4*(D+1))) (v : ℕ→Parts) : ℕ→Table (4*(D+1))
  | 0 => b
  | k+1 => monomialRowTable a (monomialPassTable a b v k) (D-1-k) (monomialPassState a v k)

def monomialPassCode : Code := countedProgram 201 monomialRowCode

theorem monomialPassTable_metadata {D : ℕ} (a b : Table (4*(D+1))) (v : ℕ→Parts) (k : ℕ) :
    (monomialPassTable a b v k).width=b.width ∧
    (monomialPassTable a b v k).basePositive=b.basePositive ∧
    (monomialPassTable a b v k).baseNegative=b.baseNegative ∧
    (monomialPassTable a b v k).baseDenominator=b.baseDenominator ∧
    (monomialPassTable a b v k).clock=b.clock := by
  induction k with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | succ k ih =>
    have ht := rowWriteTable_metadata (monomialPassTable a b v k) 4 (D-1-k)
      monomialWritePlan (monomialRowState a (D-1-k) (monomialPassState a v k))
    exact ⟨ht.1.trans ih.1,ht.2.1.trans ih.2.1,ht.2.2.1.trans ih.2.2.1,
      ht.2.2.2.1.trans ih.2.2.2.1,ht.2.2.2.2.trans ih.2.2.2.2⟩

theorem monomialPass_executes {D W : ℕ} (a b : Table (4*(D+1))) (coeff : ℕ→Parts)
    (hw : ∀j<D,(coeff j).Width W) (hc : ∀j,(coeff j).Valid) (j : ℕ) (hj : j<D)
    (hstored : MonomialStored a (monomialState D coeff j))
    (haMeta : a.MetadataWidth (monomialWorkingWidth D W))
    (hbMeta : b.MetadataWidth (monomialWorkingWidth D W))
    (hpositive : 0<addressValue b.width) (hslot : monomialWorkingWidth D W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b) (v : ℕ→Parts)
    (hv : WidthBank (Finset.range 8) (monomialStorageWidth D W) v)
    (hg : Good (Finset.range 8) v) (h4 : v 4=coeff j) (h5 : v 5=Parts.literal 2)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤monomialWorkingWidth D W) (s : Store) (hn : addressValue xs=D)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready (Finset.range 8) v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t finalWord, Executes input tape monomialPassCode cost s t ∧
      cost≤(D+1)*(13*xs.length+15)+D*(2^112*(monomialWorkingWidth D W+16)^2) ∧
      RationalDataflow.Ready (Finset.range 8) (monomialPassState a v D) t ∧ a.Ready t ∧
      (monomialPassTable a b v D).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤D ∧
    RationalDataflow.Ready (Finset.range 8) (monomialPassState a v (D-remaining)) st ∧ a.Ready st ∧
      (monomialPassTable a b v (D-remaining)).OutputReady st ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank st.val i)
  have stable : ∀r s t,CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t f hh
    refine ⟨hh.1,RationalDataflow.Ready.count_frame _ _ _ (outside_workspace _ _ (by decide))
      hh.2.1 f,hh.2.2.1.count_frame f,hh.2.2.2.1.count_frame f,?_⟩
    intro i hi
    apply RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i _) (hh.2.2.2.2 i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have step : ∀r ys st,inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost t,Executes input tape monomialRowCode cost st t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧
        cost≤2^112*(monomialWorkingWidth D W+16)^2 := by
    intro r ys st hh hword hvalue hlength
    have hr : r<D := by have := hh.1;omega
    let k := D-(r+1)
    have hk : k<D := by dsimp [k];omega
    have hindex : D-1-k=r := by dsimp [k];omega
    have hnext : k+1=D-r := by dsimp [k];omega
    have hi := monomialPassState_invariant a coeff hw hc j hj hstored v hv hg h4 h5 k hk.le
    have ht := monomialPassState_trace a coeff hw hc j hj hstored v hv hg h4 h5 k hk
    have hgood := monomialLoaded_good a coeff hc j hstored ⟨r,hr⟩ _ hi.2.1
    rw [hindex] at ht
    have hwide : monomialStorageWidth D W≤monomialWorkingWidth D W := by
      unfold monomialWorkingWidth
      omega
    obtain ⟨mw,mp,mn,md,mc⟩ := monomialPassTable_metadata a b v k
    have hmeta : (monomialPassTable a b v k).MetadataWidth (monomialWorkingWidth D W) :=
      ⟨by simpa only [mw] using hbMeta.width,by simpa only [mp] using hbMeta.basePositive,
        by simpa only [mn] using hbMeta.baseNegative,by simpa only [md] using hbMeta.baseDenominator,
        by simpa only [mc] using hbMeta.clock⟩
    have sep : (monomialPassTable a b v k).Separated := by
      simpa only [Table.Separated,mw,mp,mn,md] using hsep
    have disjoint : a.SeparatedFrom (monomialPassTable a b v k) := by
      simpa only [Table.SeparatedFrom,mw,mp,mn,md] using hdisjoint
    obtain ⟨cost,t,hex,hcost,bt,at',bot,zt,ft⟩ := monomialRow_executes a
      (monomialPassTable a b v k) (monomialWorkingWidth D W) haMeta hmeta
      (by simpa only [mw] using hpositive) (by simpa only [mw] using hslot)
      sep disjoint (monomialPassState a v k) (hi.1.mono hwide) r hr ht hgood input tape ys
      (by omega) hvalue st hh.2.1 hh.2.2.1 hh.2.2.2.1 ⟨origin,hword⟩ hh.2.2.2.2
    have bs : RationalDataflow.Ready (Finset.range 8) (monomialPassState a v (D-r)) t := by
      rw [←hnext,monomialPassState_succ,hindex]
      exact bt
    have bo : (monomialPassTable a b v (D-r)).OutputReady t := by
      rw [←hnext,monomialPassTable,hindex]
      exact bot
    exact ⟨cost,t,hex,⟨by omega,bs,at',bo,zt⟩,(ft 201 (by decide) (by decide)).trans hword,hcost⟩
  obtain ⟨cost,t,finalWord,hex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin
    monomialRowCode input tape xs.length inv (fun _ => 2^112*(monomialWorkingWidth D W+16)^2)
    stable step D xs s hn hcount rfl ⟨le_rfl,by simpa only [Nat.sub_self,monomialPassState,rowIterate] using hs,
      ha,by simpa only [Nat.sub_self,monomialPassTable] using hb,hblank⟩
  refine ⟨cost,t,finalWord,hex,?_,?_,hfinal.2.2.1,?_,hfinal.2.2.2.2,hword,hl⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost
  · simpa only [Nat.sub_zero] using hfinal.2.1
  · simpa only [Nat.sub_zero] using hfinal.2.2.2.1

#print axioms monomialPass_executes
end Maxwell.Continuum.Calibration.RawCutoff
