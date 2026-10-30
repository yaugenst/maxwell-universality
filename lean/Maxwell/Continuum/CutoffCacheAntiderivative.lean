import Maxwell.Continuum.CutoffAntiderivativeFitted
import Maxwell.Continuum.CutoffMonomialCache
import Maxwell.Continuum.RationalDataflowTablePrefix
import Maxwell.Continuum.RationalDataflowBankPartition
import Maxwell.Continuum.CutoffGeneratedCoefficients

/-! The spare polynomial buffer is reused for the literal antiderivative
coefficients. Its existing capacity is proved sufficient for every output. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

def MonomialCache.antiderivativeTable {D : ℕ} (a : MonomialCache D) : Table D :=
  (a.spare.prefix D (by omega)).filled (monomialAntiderivativeValues a.current) 0

def MonomialCache.antiderivativeBank {D : ℕ} (a : MonomialCache D) : ℕ→Parts :=
  iterate (monomialTotalTable a.current) 1 antiderivativeScaleControl (scaleInitial D) D

theorem cache_antiderivative_widths (D W : ℕ) :
    monomialWorkingWidth D W≤scaleWorkingWidth D (monomialStorageWidth D W) ∧
    scaleStateWidth D (monomialStorageWidth D W)≤monomialWorkingWidth D W := by
  unfold monomialWorkingWidth scaleWorkingWidth scaleStateWidth monomialStorageWidth
  omega

theorem MonomialCache.antiderivative_executes {D W : ℕ} (a : MonomialCache D)
    (coeff : ℕ→Parts) (hD : 0<D) (hv : a.Valid W coeff D)
    (hw : ∀k<D,(coeff k).Width W) (hg : ∀k,(coeff k).Valid)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool)
    (hlen : xs.length≤monomialWorkingWidth D W) (hn : addressValue xs=D)
    (s : Store) (hr : a.Ready W D xs s) :
    ∃cost t word,Executes input tape antiderivativePreparationCode cost s t ∧
      cost≤antiderivativePreparationCost D (monomialStorageWidth D W) xs.length
        (monomialWorkingWidth D W) ∧
      RationalDataflow.Ready scaleSlots a.antiderivativeBank t ∧
      a.antiderivativeTable.Ready t ∧ a.current.OutputReady t ∧
      BankArray.Word t.val 206 xs ∧ BankArray.Word t.val 201 word ∧
      word.length=xs.length ∧ RationalAccumulator.Blank t.val 216 ∧
      a.antiderivativeTable.MetadataWidth (scaleWorkingWidth D (monomialStorageWidth D W)) ∧
      WidthBank scaleSlots (scaleStateWidth D (monomialStorageWidth D W)) a.antiderivativeBank ∧
      Good scaleSlots a.antiderivativeBank ∧
      (∀i:Fin D,(a.antiderivativeTable.get i).Width (scaleStateWidth D (monomialStorageWidth D W)) ∧
        (a.antiderivativeTable.get i).Valid ∧
        a.antiderivativeTable.get i=monomialAntiderivativeValues a.current i) := by
  let S := monomialStorageWidth D W
  let b := a.spare.prefix D (by omega)
  have width : ∀i:Fin D,(a.current.getD (4*i.val+6)).Width S := by
    intro i
    rw [(hv.stored.2 i).2.2]
    exact (monomialState_row_width D W coeff hw D le_rfl i).2.2
  have valid : ∀i:Fin D,(a.current.getD (4*i.val+6)).Valid := by
    intro i
    rw [(hv.stored.2 i).2.2]
    exact monomialState_total_valid D coeff D (fun k _=>hg k) i
  have hB := (cache_antiderivative_widths D W).1
  have hslot : scaleStateWidth D S≤addressValue b.width :=
    (cache_antiderivative_widths D W).2.trans hv.spareSlot
  have subset : scaleSlots⊆Finset.range 8 := by decide
  obtain ⟨ys,hys,count⟩ := hr.count
  obtain ⟨cost,t,word,ex,hcost,rt,at',out,saved,count',hl,swap⟩ :=
    antiderivativePreparation_fitted_executes a.current b S hD width valid
      (hv.currentMetadata.mono hB) ((hv.spareMetadata.prefix (by omega)).mono hB)
      hslot (hv.spareSeparated.prefix (by omega)) (hv.disjoint.prefix_right (by omega))
      a.bank (fun i hi=>hv.bankWidth i (subset hi)) (fun i hi=>hv.bankGood i (subset hi))
      input tape xs ys (hlen.trans hB) s hn hr.saved count (hr.bank.restrict subset)
      hr.current (hr.spare.prefix (by omega)) hr.indexBlanks hr.swapBlank
  have wh (i : Fin D) : ((monomialTotalTable a.current).get i).Width S := by
    rw [monomialTotalTable_get]
    exact width i
  have vh (i : Fin D) : ((monomialTotalTable a.current).get i).Valid := by
    rw [monomialTotalTable_get]
    exact valid i
  refine ⟨cost,t,word,ex,hcost.trans ?_,rt,at',out,saved,count',hl,swap,?_,
    scale_iterate_width (monomialTotalTable a.current) S wh D le_rfl,
    scale_iterate_good (monomialTotalTable a.current) vh D le_rfl,?_⟩
  · change antiderivativePreparationCost D S xs.length ys.length≤
      antiderivativePreparationCost D S xs.length (monomialWorkingWidth D W)
    unfold antiderivativePreparationCost scalePreparationCost
    omega
  · have hm := (hv.spareMetadata.prefix (show D≤4*(D+1) by omega)).mono hB
    exact ⟨hm.width,hm.basePositive,hm.baseNegative,hm.baseDenominator,hm.clock⟩
  · exact monomialAntiderivative_output a.current b S width valid hslot

#print axioms MonomialCache.antiderivative_executes
end Maxwell.Continuum.Calibration.RawCutoff
