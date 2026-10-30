import Maxwell.Continuum.CalibrationRootTableRefresh

/-! One actual traversal body imports the current runtime index, computes
and writes its coefficient, and restores the reusable small input banks. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def bodyCode : Code := .seq (NaturalImport.code 201 330) (.seq emitCode refreshCode)
def bodyCost (grid N B I W length : ℕ) : ℕ := 31*length+39+
  emitCost grid N B I W+refreshCost grid N B I

def indexedNaturals (grid index : ℕ) : ℕ→ℕ := Function.update (RootReset.naturals grid) 330 index

theorem indexed_width (grid index B : ℕ) (hg : grid.bits.length≤B) (hi : index.bits.length≤B) :
    ∀i∈RootFrequency.ids,(indexedNaturals grid index i).bits.length≤B := by
  intro i hm
  by_cases he : i=330
  · subst i
    exact hi
  · simpa only [indexedNaturals,Function.update_of_ne he] using RootReset.naturals_width grid B hg i hm

theorem indexed_zero (grid index : ℕ) :
    ∀i∈NaturalQuotient.workPorts,indexedNaturals grid index i=0 := by
  intro i hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  simp only [indexedNaturals,Function.update_of_ne (by omega : i≠330),RootReset.naturals,
    ite_eq_right (by omega : i≠331)]

theorem body_executes {T : ℕ} (a : PartArray.Table T) (target : Fin T)
    (grid degree N B I W : ℕ) [NeZero grid] (hgrid : grid=2*degree+1) (hB : 2≤B) (hI : 1≤I)
    (hg : grid.bits.length≤B) (ht : target.val.bits.length≤B)
    (scale : Parts) (hscale : scale.Valid) (hscaleWidth : scale.Width I)
    (hm : a.MetadataWidth W) (hfit : entryWidth grid N B I≤addressValue a.width) (hsep : a.Separated)
    (index : List Bool) (hindex : addressValue index=target.val) (hlen : index.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hctx : Context RootReset.bank N (RootReset.naturals grid) (RootReset.parts scale) s)
    (ha : a.OutputReady s) (hi : BankArray.Word s.val 201 index) :
    ∃(cost : ℕ) (t : Store) (entry : Parts),
      Executes input tape bodyCode cost s t ∧ cost≤bodyCost grid N B I W index.length ∧
      entry.Valid ∧ entry.Width (entryWidth grid N B I) ∧
      entry.value=scalar grid scale.value N target.val ∧
      Context RootReset.bank N (RootReset.naturals grid) (RootReset.parts scale) t ∧
      (a.set target entry).OutputReady t ∧
      t.val.memory=a.writeMemory target entry s.val.memory ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.output=s.val.output := by
  obtain ⟨c0,s0,e0,h0,b0,f0⟩ := NaturalImport.executes RootFrequency.ids 201 330 (by decide) (by decide)
    (RootReset.naturals grid) index input tape s hctx.natural hi
  have b0' : NatAssign.Bank RootFrequency.ids (indexedNaturals grid target.val) s0.val := by
    simpa only [indexedNaturals,hindex] using b0
  have z0 (i : ℕ) (hi' : i<5) : Blank s0.val i :=
    blank_of_eq (f0.tapes i (by simp only [Finset.mem_singleton];omega)) (hctx.scratch i hi')
  have f0' : BinaryPrecision.Frame RootFrequency.changed s.val s0.val := f0.mono (by decide)
  have ctx0 := hctx.natural_frame f0' b0' z0
  have a0 := RootFrequency.output_frame ha f0' z0
  have i0 := BankArray.word_of_eq (f0.tapes 201 (by decide)) hi
  have hw := RootReset.parts_width scale I hI hscaleWidth
  have good := RootReset.parts_good scale hscale
  obtain ⟨c1,s1,out,e1,h1,m1,t1,o1⟩ := emit_executes a target RootReset.bank (by decide) (by decide)
    grid degree N B I W hgrid hB hI (indexedNaturals grid target.val) (RootReset.parts scale)
    (by simp [indexedNaturals,RootReset.naturals]) (by simp [indexedNaturals])
    (indexed_width grid target.val B hg ht) (indexed_zero grid target.val) hw good hm hfit hsep
    index hindex hlen input tape s0 ctx0 a0 i0
  have scaleEq : RootReset.parts scale 9=scale := by simp only [RootReset.parts,ite_true]
  have outScale : (RootReset.parts scale 9).Width I := by rw [scaleEq];exact hscaleWidth
  obtain ⟨c2,t,e2,h2,ctx2,a2,f2⟩ := out.refresh_executes hI outScale input tape s1
  have ctx2' : Context RootReset.bank N (RootReset.naturals grid) (RootReset.parts scale) t := by
    simpa only [scaleEq] using ctx2
  refine ⟨c0+(c1+c2),t,out.entry,e0.seq (e1.seq e2),?_,?_,?_,?_,ctx2',a2,?_,?_,?_⟩
  · simp only [RootReset.naturals,show (330:ℕ)≠331 by decide,ite_false,
      show (0:ℕ).bits.length=0 by rfl] at h0
    unfold bodyCost
    omega
  · rw [out.entry_eq]
    exact out.good 12 (by decide)
  · rw [out.entry_eq]
    exact out.width 12 (by decide)
  · simpa only [scaleEq] using out.value
  · rw [f2.memory,m1,f0.memory]
  · exact (f2.tapes 201 (RootGrid.coefficient_protected RootReset.bank 201 (by simp))).trans
      (t1.trans (f0.tapes 201 (by decide)))
  · exact f2.output.trans (o1.trans f0.output)

#print axioms body_executes
end Maxwell.Continuum.RationalDataflow.RootTable
