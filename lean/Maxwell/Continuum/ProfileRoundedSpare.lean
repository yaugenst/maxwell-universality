import Maxwell.Continuum.ProfileTableSpareFrame

/-! The computed rounded table retains the second buffer used by endpoint
correction. Every stored row is produced by the fixed runtime sampler. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

theorem rounded_table_spare_executes (grid D P U M : ℕ) (a b : PartArray.Table D)
    (hg0 : 0<grid) (hg : grid≤U) (hD : D≤U) (hP : P≤U)
    (hmeta : a.MetadataWidth M) (hfit : roundedRawWidth U≤addressValue a.width)
    (hsep : a.Separated) (hdis : b.SeparatedFrom a)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤M) (hvalue : addressValue xs=D) (s : Store)
    (hp : ProducerState grid D P U s) (ha : a.OutputReady s) (hb : b.Ready s)
    (hsize : Word s.val 661 D) (hblank : Blank s.val 216)
    (hcounter : s.val.tapes 700=BitTape.shifted xs origin) :
    ∃(cost : ℕ) (t : Store) (finalWord : List Bool) (_result : RoundedTableState grid D P U a 0 t),
      Executes input tape roundedTableCode cost s t ∧
      t.val.tapes 700=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      cost≤roundedTableCost grid D P U M xs.length ∧
      b.Ready t ∧ Word t.val 661 D ∧ Blank t.val 216 := by
  let inv (remaining : ℕ) (t : Store) :=
    Nonempty (RoundedTableState grid D P U a remaining t) ∧
      b.Ready t ∧ Word t.val 661 D ∧ Blank t.val 216
  have stable : ∀r s t,CountedShifted.Frame 700 s t→inv r s→inv r t := by
    intro r s t f h
    obtain ⟨⟨h⟩,hb,hs,hz⟩ := h
    exact ⟨⟨h.count_frame f⟩,inputReady_count700 hb f,
      word_of_eq (f.2.2.2.2.2.1 661 (by decide)) hs,
      blank_of_eq (f.2.2.2.2.2.1 216 (by decide)) hz⟩
  have step : ∀r ys st,inv (r+1) st→st.val.tapes 700=BitTape.shifted ys origin→
      addressValue ys=r→ys.length=xs.length→
      ∃cost t,Executes input tape roundedStoreCode cost st t ∧ inv r t ∧
        t.val.tapes 700=BitTape.shifted ys origin ∧
        cost≤roundedStoreCost grid D P U (roundedWidth grid U) M xs.length (roundedWidth grid U) := by
    intro r ys st hh hword hval hlength
    obtain ⟨⟨h⟩,spare,size,blank⟩ := hh
    have hr : r<D := by have := h.bound;omega
    let index : Fin D := ⟨r,hr⟩
    have fit : roundedRawWidth U≤addressValue h.table.width := by simpa only [h.metadata.1] using hfit
    obtain ⟨cost,t,word,saved,out,e,output,count,len,_,indexFrame,gridWord,stored,savedWidth,mem,hc⟩ :=
      rounded_store_executes h.table grid D P U (roundedWidth grid U) M index hg0 hg hD hP
        (by dsimp [index];omega) (by unfold roundedWidth;omega)
        h.values h.width h.saved h.savedWidth ys h.innerWord hval (by omega)
        (tableMetadata_width h.metadata hmeta) fit (tableMetadata_separated h.metadata hsep)
        input tape st h.ready h.phaseClean h.glueClean h.floorClean h.power h.parameters h.gridWord
        ⟨origin,hword⟩ h.innerCounter h.stored h.output
    have frameCount : t.val.tapes 700=BitTape.shifted ys origin := indexFrame.trans hword
    have ready : ProducerState grid D P U t :=
      ⟨out.values,out.ready,out.width,saved,stored,savedWidth.mono (by
          unfold roundedWidth cosineWidth;omega),word,count,by
          rw [len]
          exact (bits_le_of_le hg).trans (by unfold roundedWidth cosineWidth dftNormalizationWidth;omega),
        out.phaseClean,out.glueClean,out.floorClean,out.parameters,out.power,gridWord⟩
    have correct : ∀i:Fin D,r ≤ i.val→((h.table.set index (out.values 9)).get i).Valid ∧
        ((h.table.set index (out.values 9)).get i).denominator=1 ∧
        ((h.table.set index (out.values 9)).get i).value=roundedTarget grid D P i.val := by
      intro i hi
      by_cases he : i=index
      · subst i
        rw [h.table.set_get index (out.values 9) (out.resultWidth.mono fit)]
        exact ⟨out.good 9 (by decide),out.resultDenominator,out.resultValue⟩
      · rw [h.table.set_get_ne index i (out.values 9) (fun hh => he hh.symm)]
        apply h.correct i
        have hne : i.val≠r := fun hv => he (Fin.ext hv)
        omega
    have spare' := roundedStore_spare_ready e spare
      (tableMetadata_separatedFrom h.metadata b hdis) index (out.values 9) mem output
    have size' := word_of_eq (roundedStore_keep e 661 (by simp [roundedStoreProtected])) size
    have blank' := blank_of_eq (roundedStore_keep e 216 (by simp [roundedStoreProtected])) blank
    refine ⟨cost,t,e,⟨⟨⟨ready,by omega,h.table.set index (out.values 9),h.metadata,output,correct⟩⟩,
      spare',size',blank'⟩,frameCount,?_⟩
    rw [hlength] at hc
    exact hc.trans (roundedStoreCost_mono_old grid D P U (roundedWidth grid U) M xs.length _ _ h.innerLength)
  obtain ⟨cost,t,finalWord,e,result,word,len,_,hc⟩ := counted_executes_sized 700 origin roundedStoreCode
    input tape xs.length inv (fun _ => roundedStoreCost grid D P U (roundedWidth grid U) M xs.length (roundedWidth grid U))
    stable step D xs s hvalue hcounter rfl ⟨⟨⟨hp,le_rfl,a,tableMetadata_refl a,ha,by
      intro i hi;have := i.isLt;omega⟩⟩,hb,hsize,hblank⟩
  obtain ⟨⟨result⟩,bt,size,blank⟩ := result
  exact ⟨cost,t,finalWord,result,e,word,len,by
    simpa only [roundedTableCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hc,bt,size,blank⟩

#print axioms rounded_table_spare_executes
end Maxwell.Continuum.Profile.Runtime
