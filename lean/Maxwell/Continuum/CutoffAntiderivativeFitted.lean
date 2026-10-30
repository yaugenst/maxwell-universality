import Maxwell.Continuum.CutoffAntiderivativePreparation
import Maxwell.Continuum.RationalDataflowRowMapFitted

/-! Reusing the spare cache only requires room for the actual output
coefficients, rather than the larger temporary arithmetic-width bound. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768
attribute [local irreducible] scaleInitial antiderivativeScaleControl

theorem monomialAntiderivative_fitted_executes {n : ℕ} (a : Table (4*(n+1))) (b : Table n)
    (W : ℕ) (hw : ∀i:Fin n,(a.getD (4*i.val+6)).Width W)
    (hv : ∀i:Fin n,(a.getD (4*i.val+6)).Valid)
    (haMeta : a.MetadataWidth (scaleWorkingWidth n W))
    (hbMeta : b.MetadataWidth (scaleWorkingWidth n W))
    (hslot : scaleStateWidth n W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤scaleWorkingWidth n W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready scaleSlots (scaleInitial n) s)
    (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t finalWord,Executes input tape monomialAntiderivativeCode cost s t ∧
      cost≤monomialAntiderivativeCost n W xs.length ∧
      RationalDataflow.Ready scaleSlots
        (iterate (monomialTotalTable a) 1 antiderivativeScaleControl (scaleInitial n) n) t ∧
      a.Ready t ∧ (b.filled (monomialAntiderivativeValues a) 0).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  have hw' : ∀i,(monomialTotalTable a).get i |>.Width W := by
    intro i
    rw [monomialTotalTable_get]
    exact hw i
  have hv' : ∀i,((monomialTotalTable a).get i).Valid := by
    intro i
    rw [monomialTotalTable_get]
    exact hv i
  have hSB : scaleStateWidth n W≤scaleWorkingWidth n W := by
    unfold scaleWorkingWidth
    omega
  obtain ⟨cost,t,finalWord,ex,hcost,rt,at',bt,zt,hword,hl⟩ := rowMap_fitted_executes a b scaleSlots
    4 3 [(6,1)] (by simp [scaleSlots]) (by decide)
    antiderivativeScaleControl antiderivativeScaleControl_valid 0 (by decide) (scaleInitial n)
    (scaleWorkingWidth n W)
    haMeta hbMeta (by unfold scaleStateWidth at hslot;omega)
    (fun k hk => by
      rw [monomialTotal_iterate a _ (k+1) (by omega)]
      exact (scale_iterate_width (monomialTotalTable a) W hw' (k+1) (by omega) 0 (by decide)).mono hslot)
    hsep hdisjoint
    (fun k hk => by
      rw [monomialTotal_iterate a _ k hk.le]
      exact (scale_iterate_width (monomialTotalTable a) W hw' k hk.le).mono hSB)
    (fun k hk => by
      rw [monomialTotal_loaded a _ k hk]
      exact scale_loaded_widthTrace (monomialTotalTable a) W hw' k hk)
    (fun k hk => by
      rw [monomialTotal_loaded a _ k hk]
      exact scale_loaded_good (monomialTotalTable a) hv' k hk)
    (fun k hk => by
      rw [monomialTotal_loaded a _ k hk]
      exact scale_loaded_admissible (monomialTotalTable a) k hk)
    (by intro k hk x hx;simp only [List.mem_singleton] at hx;subst x;simp only;omega)
    input tape xs origin hlen s hn hcount hs ha hb hblank
  refine ⟨cost,t,finalWord,ex,hcost,?_,at',bt,zt,hword,hl⟩
  simpa only [monomialTotal_iterate a _ n le_rfl] using rt


theorem antiderivativePreparation_fitted_executes {n : ℕ} (a : Table (4*(n+1))) (b : Table n)
    (W : ℕ) (hnpos : 0<n)
    (hw : ∀i:Fin n,(a.getD (4*i.val+6)).Width W)
    (hv : ∀i:Fin n,(a.getD (4*i.val+6)).Valid)
    (haMeta : a.MetadataWidth (scaleWorkingWidth n W))
    (hbMeta : b.MetadataWidth (scaleWorkingWidth n W))
    (hslot : scaleStateWidth n W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (v : ℕ→Parts) (hvw : WidthBank scaleSlots W v) (hvg : Good scaleSlots v)
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool)
    (hlen : xs.length≤scaleWorkingWidth n W) (s : Store) (hn : addressValue xs=n)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys)
    (hs : RationalDataflow.Ready scaleSlots v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i)
    (hswap : RationalAccumulator.Blank s.val 216) :
    ∃ cost t finalWord,Executes input tape antiderivativePreparationCode cost s t ∧
      cost≤antiderivativePreparationCost n W xs.length ys.length ∧
      RationalDataflow.Ready scaleSlots
        (iterate (monomialTotalTable a) 1 antiderivativeScaleControl (scaleInitial n) n) t ∧
      (b.filled (monomialAntiderivativeValues a) 0).Ready t ∧ a.OutputReady t ∧
      BankArray.Word t.val 206 xs ∧ BankArray.Word t.val 201 finalWord ∧
      finalWord.length=xs.length ∧ RationalAccumulator.Blank t.val 216 := by
  obtain ⟨c0,s0,e0,hc0,r0,saved0,count0⟩ := scalePreparation_executes n W hnpos v hvw hvg
    input tape xs ys hn s hs hsaved hcount
  have a0 := scalePreparation_table_frame ha e0 r0.2
  have b0 := scalePreparation_output_frame hb e0 a0.scratch a0.seven
  have z0 : ∀i∈RowIndex.ids,RationalAccumulator.Blank s0.val i := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (scalePreparation_keeps e0 i _) (hblank i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> simp
  have swap0 := RationalAccumulator.blank_of_eq (scalePreparation_keeps e0 216 (by simp)) hswap
  obtain ⟨origin,count0⟩ := count0
  obtain ⟨c1,s1,finalWord,e1,hc1,r1,a1,b1,_,count1,hl⟩ := monomialAntiderivative_fitted_executes a b W hw hv
    haMeta hbMeta hslot hsep hdisjoint input tape xs origin hlen s0 hn count0 r0 a0 b0 z0
  have saved1 := BankArray.word_of_eq (e1.protectsTape 206 monomialAntiderivative_protects_saved) saved0
  have swap1 := RationalAccumulator.blank_of_eq
    (e1.protectsTape 216 monomialAntiderivative_protects_swap) swap0
  have meta1 : (b.filled (monomialAntiderivativeValues a) 0).MetadataWidth (scaleWorkingWidth n W) :=
    ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩
  obtain ⟨c2,t,e2,hc2,rt,bt,at',zt,ft⟩ := headerSwap_executes a
    (b.filled (monomialAntiderivativeValues a) 0) (scaleWorkingWidth n W) haMeta meta1
    scaleSlots _ input tape s1 r1 a1 b1 swap1
  refine ⟨c0+(c1+c2),t,finalWord,e0.seq (e1.seq e2),?_,rt,bt,at',?_,?_,hl,zt⟩
  · unfold antiderivativePreparationCost
    omega
  · exact BankArray.word_of_eq (ft.tapes 206 (by decide)) saved1
  · exact BankArray.word_of_eq (ft.tapes 201 (by decide)) ⟨origin,count1⟩


#print axioms antiderivativePreparation_fitted_executes
end Maxwell.Continuum.Calibration.RawCutoff
