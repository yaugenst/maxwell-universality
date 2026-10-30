import Maxwell.Continuum.CutoffMonomialPrepare
import Maxwell.Continuum.RationalDataflowTableHeaderSwap

/-! The two literal cache buffers and arithmetic bank, with a proved
invariant for each completed outer Chebyshev step. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

structure MonomialCache (D : ℕ) where
  current : Table (4*(D+1))
  spare : Table (4*(D+1))
  bank : ℕ→Parts

def MonomialCache.prepared {D : ℕ} (a : MonomialCache D) (j : ℕ) : ℕ→Parts :=
  Function.update a.bank 4 (a.current.getD (4*j+7))

def MonomialCache.next {D : ℕ} (a : MonomialCache D) (j : ℕ) : MonomialCache D :=
  ⟨monomialPassTable a.current a.spare (a.prepared j) D,a.current,
    monomialPassState a.current (a.prepared j) D⟩

structure MonomialCache.Valid {D : ℕ} (a : MonomialCache D) (W : ℕ) (coeff : ℕ→Parts) (j : ℕ) : Prop where
  currentMetadata : a.current.MetadataWidth (monomialWorkingWidth D W)
  spareMetadata : a.spare.MetadataWidth (monomialWorkingWidth D W)
  currentSlot : monomialWorkingWidth D W≤addressValue a.current.width
  spareSlot : monomialWorkingWidth D W≤addressValue a.spare.width
  currentSeparated : a.current.Separated
  spareSeparated : a.spare.Separated
  disjoint : a.current.SeparatedFrom a.spare
  stored : MonomialStored a.current (monomialState D coeff j)
  sentinel : a.spare.getD 1=Parts.literal 0
  currentCoefficients : MonomialCoefficientsStored a.current coeff
  spareCoefficients : MonomialCoefficientsStored a.spare coeff
  bankWidth : WidthBank (Finset.range 8) (monomialStorageWidth D W) a.bank
  bankGood : Good (Finset.range 8) a.bank
  two : a.bank 5=Parts.literal 2

theorem MonomialCache.prepared_eq {D W : ℕ} {a : MonomialCache D} {coeff : ℕ→Parts} {j : ℕ}
    (ha : a.Valid W coeff j) (hj : j<D) : a.prepared j=Function.update a.bank 4 (coeff j) := by
  rw [MonomialCache.prepared,ha.currentCoefficients ⟨j,hj⟩]

theorem MonomialCache.prepared_bounds {D W : ℕ} {a : MonomialCache D} {coeff : ℕ→Parts} {j : ℕ}
    (ha : a.Valid W coeff j) (hj : j<D) (hw : ∀r<D,(coeff r).Width W) (hc : ∀r,(coeff r).Valid) :
    WidthBank (Finset.range 8) (monomialStorageWidth D W) (a.prepared j) ∧
    Good (Finset.range 8) (a.prepared j) ∧ a.prepared j 4=coeff j ∧ a.prepared j 5=Parts.literal 2 := by
  rw [a.prepared_eq ha hj]
  exact ⟨ha.bankWidth.update 4 ((hw j hj).mono (by unfold monomialStorageWidth;omega)),
    ha.bankGood.update 4 (hc j),Function.update_self _ _ _,
    (Function.update_of_ne (by decide) _ _).trans ha.two⟩

theorem MonomialCache.Valid.next {D W : ℕ} {a : MonomialCache D} {coeff : ℕ→Parts} {j : ℕ}
    (ha : a.Valid W coeff j) (hj : j<D) (hw : ∀r<D,(coeff r).Width W) (hc : ∀r,(coeff r).Valid) :
    (a.next j).Valid W coeff (j+1) := by
  have hp := a.prepared_bounds ha hj hw hc
  have hfinal := monomialPassState_invariant a.current coeff hw hc j hj ha.stored
    (a.prepared j) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 D le_rfl
  obtain ⟨mw,mp,mn,md,mc⟩ := monomialPassTable_metadata a.current a.spare (a.prepared j) D
  have hstorage : monomialStorageWidth D W≤monomialWorkingWidth D W := by
    unfold monomialWorkingWidth;omega
  refine ⟨?_,ha.currentMetadata,?_,ha.currentSlot,?_,ha.currentSeparated,?_,?_,ha.stored.1,
    MonomialCoefficientsStored.pass a.current a.spare coeff ha.spareCoefficients (a.prepared j) D,
    ha.currentCoefficients,hfinal.1,hfinal.2.1,hfinal.2.2.2⟩
  · exact ⟨by simpa only [MonomialCache.next,mw] using ha.spareMetadata.width,
      by simpa only [MonomialCache.next,mp] using ha.spareMetadata.basePositive,
      by simpa only [MonomialCache.next,mn] using ha.spareMetadata.baseNegative,
      by simpa only [MonomialCache.next,md] using ha.spareMetadata.baseDenominator,
      by simpa only [MonomialCache.next,mc] using ha.spareMetadata.clock⟩
  · simpa only [MonomialCache.next,mw] using ha.spareSlot
  · simpa only [MonomialCache.next,Table.Separated,mw,mp,mn,md] using ha.spareSeparated
  · change (monomialPassTable a.current a.spare (a.prepared j) D).SeparatedFrom a.current
    simp only [Table.SeparatedFrom,mw,mp,mn,md]
    intro x hx y hy
    exact (ha.disjoint y hy x hx).symm
  · exact monomialPassTable_stored a.current a.spare coeff hw hc j hj ha.stored
      (a.prepared j) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 (hstorage.trans ha.spareSlot) ha.sentinel

structure MonomialCache.Ready {D : ℕ} (a : MonomialCache D) (W j : ℕ) (xs : List Bool) (s : Store) : Prop where
  bank : RationalDataflow.Ready (Finset.range 8) a.bank s
  current : a.current.Ready s
  spare : a.spare.OutputReady s
  indexBlanks : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i
  swapBlank : RationalAccumulator.Blank s.val 216
  saved : BankArray.Word s.val 206 xs
  count : ∃ys,ys.length≤monomialWorkingWidth D W ∧ BankArray.Word s.val 201 ys
  index : RationalAccumulator.Word s.val 208 j
  one : RationalAccumulator.Word s.val 209 1

#print axioms MonomialCache.Valid.next
end Maxwell.Continuum.Calibration.RawCutoff
