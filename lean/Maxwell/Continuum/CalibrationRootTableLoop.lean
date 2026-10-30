import Maxwell.Continuum.CalibrationRootTableBody

/-! Fixed runtime traversal of the full root coefficient array. All body
correctness and raw-width invariants are discharged by the actual evaluator. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192
attribute [local irreducible] bodyCode

def tableCode : Code := countedProgram 201 bodyCode
def tableCost (T grid N B I W length : ℕ) : ℕ :=
  (T+1)*(13*length+15)+T*bodyCost grid N B I W length

theorem Context.count_frame {S : Finset ℕ} {N : ℕ} {n : ℕ→ℕ} {v : ℕ→Parts}
    {s t : Store} (h : Context S N n v s) (f : CountedShifted.Frame 201 s t) :
    Context S N n v t := by
  have keep (i : ℕ) (hi : i≠201) := f.2.2.2.2.2.1 i hi
  refine ⟨h.rational.count_frame S v 201 (RootGrid.coefficient_protected S 201 (by simp) ∘
    (fun hm => Finset.mem_union_left _ (Finset.mem_union_right _ hm))) f,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have hh := RootFrequency.ids_bounds i hi
    exact word_of_eq (keep i (by omega)) (h.natural i hi)
  · intro i hi
    exact blank_of_eq (keep i (by omega)) (h.scratch i hi)
  · intro i hi
    have ho : i≠201 := by
      intro he;subst i
      exact (show 201∉GlueMachine.Runtime.ids.erase 640 by decide) hi
    exact blank_of_eq (keep i ho) (h.glue i hi)
  · intro i hi
    have ho : i≠201 := by
      intro he;subst i
      exact (show 201∉(PhaseMachine.Runtime.ids.erase 652).erase 653 by decide) hi
    exact blank_of_eq (keep i ho) (h.phase i hi)
  · exact word_of_eq (keep 640 (by decide)) h.glue_precision
  · exact word_of_eq (keep 652 (by decide)) h.phase_range
  · exact word_of_eq (keep 653 (by decide)) h.phase_precision

structure TableState (T grid N B I W : ℕ) [NeZero grid] (scale : Parts) (remaining : ℕ) (s : Store) where
  table : PartArray.Table T
  remaining_le : remaining≤T
  context : Context RootReset.bank N (RootReset.naturals grid) (RootReset.parts scale) s
  ready : table.OutputReady s
  metadata : table.MetadataWidth W
  fit : entryWidth grid N B I≤addressValue table.width
  separated : table.Separated
  correct : ∀i : Fin T, remaining ≤ i.val →
    (table.get i).Valid ∧ (table.get i).Width (entryWidth grid N B I) ∧
      (table.get i).value=scalar grid scale.value N i.val

def TableState.count_frame {T grid N B I W : ℕ} [NeZero grid] {scale : Parts} {remaining : ℕ}
    {s t : Store} (h : TableState T grid N B I W scale remaining s) (f : CountedShifted.Frame 201 s t) :
    TableState T grid N B I W scale remaining t where
  table := h.table
  remaining_le := h.remaining_le
  context := h.context.count_frame f
  ready := h.ready.count_frame f
  metadata := h.metadata
  fit := h.fit
  separated := h.separated
  correct := h.correct

theorem TableState.step_executes {T grid N B I W : ℕ} [NeZero grid] {scale : Parts}
    {remaining : ℕ} (degree : ℕ) (hgrid : grid=2*degree+1) (hB : 2≤B) (hI : 1≤I)
    (hg : grid.bits.length≤B) (hT : T.bits.length≤B)
    (hscale : scale.Valid) (hscaleWidth : scale.Width I)
    (index : List Bool) (hindex : addressValue index=remaining) (hlen : index.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : TableState T grid N B I W scale (remaining+1) s) (hi : BankArray.Word s.val 201 index) :
    ∃cost t,Executes input tape bodyCode cost s t ∧ cost≤bodyCost grid N B I W index.length ∧
      Nonempty (TableState T grid N B I W scale remaining t) ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.output=s.val.output := by
  have hr : remaining<T := by have hh := h.remaining_le;omega
  let target : Fin T := ⟨remaining,hr⟩
  have ht : target.val.bits.length≤B := (RationalWords.bits_mono (Nat.le_of_lt hr)).trans hT
  obtain ⟨c,t,entry,e,hc,valid,width,value,ctx,out,_,hcounter,hout⟩ := body_executes h.table target
    grid degree N B I W hgrid hB hI hg ht scale hscale hscaleWidth h.metadata h.fit h.separated
    index hindex hlen input tape s h.context h.ready hi
  let next : TableState T grid N B I W scale remaining t := {
    table := h.table.set target entry
    remaining_le := Nat.le_of_lt hr
    context := ctx
    ready := out
    metadata := ⟨h.metadata.width,h.metadata.basePositive,h.metadata.baseNegative,
      h.metadata.baseDenominator,h.metadata.clock⟩
    fit := h.fit
    separated := h.separated
    correct := by
      intro j hj
      by_cases he : j=target
      · subst j
        rw [h.table.set_get target entry (width.mono h.fit)]
        exact ⟨valid,width,value⟩
      · rw [h.table.set_get_ne target j entry (Ne.symm he)]
        have hj' : remaining+1≤j.val := by
          have hne : j.val≠remaining := by intro hev;apply he;exact Fin.ext hev
          omega
        exact h.correct j hj' }
  exact ⟨c,t,e,hc,⟨next⟩,hcounter,hout⟩

theorem table_executes {T : ℕ} (a : PartArray.Table T)
    (grid degree N B I W : ℕ) [NeZero grid] (hgrid : grid=2*degree+1) (hB : 2≤B) (hI : 1≤I)
    (hg : grid.bits.length≤B) (hT : T.bits.length≤B)
    (scale : Parts) (hscale : scale.Valid) (hscaleWidth : scale.Width I)
    (hm : a.MetadataWidth W) (hfit : entryWidth grid N B I≤addressValue a.width) (hsep : a.Separated)
    (index : List Bool) (origin : ℤ) (hindex : addressValue index=T) (hlen : index.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hctx : Context RootReset.bank N (RootReset.naturals grid) (RootReset.parts scale) s)
    (ha : a.OutputReady s) (hi : s.val.tapes 201=BitTape.shifted index origin) :
    ∃cost t finalWord,Executes input tape tableCode cost s t ∧
      Nonempty (TableState T grid N B I W scale 0 t) ∧
      cost≤tableCost T grid N B I W index.length ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=index.length ∧
      t.val.output=s.val.output := by
  let inv : ℕ→Store→Prop := fun remaining st =>
    Nonempty (TableState T grid N B I W scale remaining st) ∧ st.val.output=s.val.output
  let bound : ℕ→ℕ := fun _ => bodyCost grid N B I W index.length
  have stable : ∀r a b,CountedShifted.Frame 201 a b → inv r a → inv r b := by
    intro r a b f hh
    rcases hh.1 with ⟨state⟩
    exact ⟨⟨state.count_frame f⟩,f.2.2.2.2.1.trans hh.2⟩
  have step : ∀r ys st,inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=index.length →
      ∃cost t,Executes input tape bodyCode cost st t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧ cost≤bound r := by
    intro r ys st hh hword hvalue hlength
    rcases hh.1 with ⟨state⟩
    obtain ⟨c,t,e,hc,ht,hcounter,hout⟩ := state.step_executes degree hgrid hB hI hg hT hscale hscaleWidth
      ys hvalue (by omega) input tape st ⟨origin,hword⟩
    exact ⟨c,t,e,⟨ht,hout.trans hh.2⟩,hcounter.trans hword,by simpa only [bound,hlength] using hc⟩
  let start : TableState T grid N B I W scale T s := {
    table := a
    remaining_le := le_rfl
    context := hctx
    ready := ha
    metadata := hm
    fit := hfit
    separated := hsep
    correct := by intro i hi';have hh := i.isLt;omega }
  obtain ⟨c,t,finalWord,e,hInv,hword,hlength,_,hc⟩ := counted_executes_sized 201 origin bodyCode
    input tape index.length inv bound stable step T index s hindex hi rfl ⟨⟨start⟩,rfl⟩
  refine ⟨c,t,finalWord,e,hInv.1,?_,hword,hlength,hInv.2⟩
  simpa only [bound,tableCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hc

#print axioms table_executes
end Maxwell.Continuum.RationalDataflow.RootTable
