import Maxwell.Continuum.RationalDataflowRowWrite
import Maxwell.Continuum.RationalDataflowSharedMapState

/-! A fixed runtime loop initializes every stored raw-rational entry.
Incoming memory may be arbitrary; all three output channels are written. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def fillCode (entry : ℕ) : Code := countedProgram 201 (rowWriteCode 1 0 entry)

theorem fill_executes {n m : ℕ} (a : Table n) (b : Table m) (S : Finset ℕ)
    (entry : ℕ) (he : entry∈S) (v : ℕ→Parts) (W : ℕ) (hbMeta : b.MetadataWidth W)
    (hpositive : 0<addressValue b.width) (hfit : (v entry).Width (addressValue b.width))
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=m)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t finalWord, Executes input tape (fillCode entry) cost s t ∧
      cost≤(m+1)*(13*xs.length+15)+m*(2^30*(W+6)^2) ∧
      RationalDataflow.Ready S v t ∧ a.Ready t ∧ (b.filled (fun _ => v entry) 0).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤m ∧
    RationalDataflow.Ready S v st ∧ a.Ready st ∧
      (b.filled (fun _ => v entry) remaining).OutputReady st ∧
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
      ∃ cost t,Executes input tape (rowWriteCode 1 0 entry) cost st t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧ cost≤2^30*(W+6)^2 := by
    intro r ys st hh hword hvalue hlength
    have hr : r<m := by have := hh.1;omega
    obtain ⟨cost,t,hex,hcost,bt,at',bot,zt,_,ft⟩ := rowWrite_executes a
      (b.filled (fun _ => v entry) (r+1)) S 1 0 entry he v hpositive hfit hsep hdisjoint
      input tape ys (by simp only [one_mul,add_zero,hvalue];exact hr) st hh.2.1 hh.2.2.1
      hh.2.2.2.1 ⟨origin,hword⟩ hh.2.2.2.2
    have output : (b.filled (fun _ => v entry) r).OutputReady t := by
      simpa only [one_mul,add_zero,hvalue,Table.filled_step] using bot
    have hp := rowWriteCost_polynomial (b.filled (fun _ => v entry) (r+1)) ys (v entry) 1 0 W
      ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩ (by omega)
    have hp' : rowWriteCost (b.filled (fun _ => v entry) (r+1)) ys (v entry) 1 0≤2^30*(W+6)^2 := by
      simpa only [show (1:ℕ).bits.length=1 from rfl,show (0:ℕ).bits.length=0 from rfl,Nat.add_zero,
        show W+1+5=W+6 by omega] using hp
    exact ⟨cost,t,hex,⟨by omega,bt,at',output,zt⟩,
      (ft.tapes 201 (by decide) (by decide) (by decide)).trans hword,hcost.trans hp'⟩
  obtain ⟨cost,t,finalWord,hex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin
    (rowWriteCode 1 0 entry) input tape xs.length inv (fun _ => 2^30*(W+6)^2) stable step
    m xs s hn hcount rfl ⟨le_rfl,hs,ha,by simpa only [Table.filled_initial] using hb,hblank⟩
  refine ⟨cost,t,finalWord,hex,?_,hfinal.2.1,hfinal.2.2.1,hfinal.2.2.2.1,hfinal.2.2.2.2,hword,hl⟩
  simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost

#print axioms fill_executes
end Maxwell.Continuum.RationalDataflow.PartArray
