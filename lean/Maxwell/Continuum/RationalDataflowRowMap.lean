import Maxwell.Continuum.RationalDataflowRowFold
import Maxwell.Continuum.RationalDataflowRowWritePlan
import Maxwell.Continuum.RationalDataflowArrayMap

/-! A fixed row-read plan, arithmetic control, and one actual output write
materialize a table in a runtime traversal. Input and output lengths may differ. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def rowMapCode (stride : ℕ) (plan : List (ℕ×ℕ)) (c : Control) (result : ℕ) : Code :=
  countedProgram 201 (.seq (rowPlanCode stride plan) (.seq c.code (rowWriteCode 1 0 result)))

def rowMapValues {m : ℕ} (a : Table m) (stride : ℕ) (plan : List (ℕ×ℕ)) (c : Control)
    (n result : ℕ) (v : ℕ→Parts) : Fin n→Parts :=
  fun i => rowIterate a stride plan c n v (n-i.val) result

def rowMapStepCost (stride O B : ℕ) (plan : List (ℕ×ℕ)) (c : Control) : ℕ :=
  rowFoldStepCost stride O B plan c+2^30*(B+6)^2

theorem rowMap_executes {m n : ℕ} (a : Table m) (b : Table n) (S : Finset ℕ)
    (stride O : ℕ) (plan : List (ℕ×ℕ)) (hp : ∀x∈plan,x.2∈S)
    (ho : ∀x∈plan,x.1.bits.length≤O) (c : Control) (hc : c.Valid S) (result : ℕ) (hr : result∈S)
    (v : ℕ→Parts) (B : ℕ) (hB : 0<B) (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hslot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hw : ∀k<n,WidthBank S B (rowIterate a stride plan c n v k))
    (ht : ∀k<n,c.WidthTrace S B (rowLoaded a stride plan c n v k))
    (hg : ∀k<n,Good S (rowLoaded a stride plan c n v k))
    (had : ∀k<n,c.AdmissibleTrace (rowLoaded a stride plan c n v k))
    (hix : ∀k<n,∀x∈plan,stride*(n-1-k)+x.1<m)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t finalWord,Executes input tape (rowMapCode stride plan c result) cost s t ∧
      cost≤(n+1)*(13*xs.length+15)+n*rowMapStepCost stride O B plan c ∧
      RationalDataflow.Ready S (rowIterate a stride plan c n v n) t ∧ a.Ready t ∧
      (b.filled (rowMapValues a stride plan c n result v) 0).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  let value := rowMapValues a stride plan c n result v
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤n ∧
    RationalDataflow.Ready S (rowIterate a stride plan c n v (n-remaining)) st ∧ a.Ready st ∧
    (b.filled value remaining).OutputReady st ∧ (∀i∈RowIndex.ids,RationalAccumulator.Blank st.val i)
  have hout : 201∉workspace S := outside_workspace _ _ (by decide)
  have stable : ∀r s t,CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t f hh
    refine ⟨hh.1,RationalDataflow.Ready.count_frame S _ 201 hout hh.2.1 f,
      hh.2.2.1.count_frame f,hh.2.2.2.1.count_frame f,?_⟩
    intro i hi
    apply RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i _) (hh.2.2.2.2 i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have step : ∀r ys st,inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost t,Executes input tape (.seq (rowPlanCode stride plan) (.seq c.code (rowWriteCode 1 0 result)))
        cost st t ∧ inv r t ∧ t.val.tapes 201=BitTape.shifted ys origin ∧
        cost≤rowMapStepCost stride O B plan c := by
    intro r ys st hh hword hvalue hlength
    have hrn : r<n := by have := hh.1;omega
    let k := n-(r+1)
    have hk : k<n := by dsimp [k];omega
    have hindex : n-1-k=r := by dsimp [k];omega
    have hnext : k+1=n-r := by dsimp [k];omega
    obtain ⟨cr,s1,er,hcr,r1,_,a1,z1,f1⟩ := rowPlan_executes a S stride O B plan hp ho haMeta
      (rowIterate a stride plan c n v k) (hw k hk) input tape ys (by omega)
      (fun x hx => by rw [hvalue,←hindex];exact hix k hk x hx)
      st hh.2.1 hh.2.2.1 ⟨origin,hword⟩ hh.2.2.2.2
    have r1' : RationalDataflow.Ready S (rowLoaded a stride plan c n v k) s1 := by
      simpa only [rowLoaded,hvalue,hindex] using r1
    have b1 := hh.2.2.2.1.rowPlan_frame f1 a1.scratch a1.seven
    obtain ⟨ca,s2,ea,hca,r2,fa⟩ := c.executes S hc _ B (ht k hk) (hg k hk) (had k hk) input tape s1 r1'
    have a2 := a1.arithmetic_frame S fa r2.2
    have b2 := b1.shared_frame S (fa.mono (workspace_subset_shared S)) a2.scratch a2.seven
    have z2 : ∀i∈RowIndex.ids,RationalAccumulator.Blank s2.val i := by
      intro i hi
      apply RationalAccumulator.blank_of_eq (fa.tapes i _) (z1 i hi)
      apply outside_workspace S i
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have fits : (rowIterate a stride plan c n v (k+1) result).Width (addressValue b.width) :=
      ((ht k hk).result result hr).mono hslot
    have count2 : s2.val.tapes 201=BitTape.shifted ys origin :=
      (fa.tapes 201 hout).trans (f1.counter.trans hword)
    obtain ⟨cw,t,ew,hcw,rt,at',bt,zt,_,fw⟩ := rowWrite_executes a (b.filled value (r+1)) S 1 0 result hr
      (rowIterate a stride plan c n v (k+1)) (lt_of_lt_of_le hB hslot) fits hsep hdisjoint
      input tape ys (by simpa only [one_mul,add_zero,hvalue] using hrn) s2 r2 a2 b2 ⟨origin,count2⟩ z2
    have hvout : rowIterate a stride plan c n v (k+1) result=value ⟨r,hrn⟩ := by
      change rowIterate a stride plan c n v (k+1) result=rowIterate a stride plan c n v (n-r) result
      rw [hnext]
    have bt' : (b.filled value r).OutputReady t := by
      simpa only [one_mul,add_zero,hvalue,hvout,Table.filled_step] using bt
    have rt' : RationalDataflow.Ready S (rowIterate a stride plan c n v (n-r)) t := by rwa [hnext] at rt
    refine ⟨cr+(ca+cw),t,er.seq (ea.seq ew),⟨by omega,rt',at',bt',zt⟩,fw.counter.trans count2,?_⟩
    have hcw' := rowWriteCost_polynomial (b.filled value (r+1)) ys
      (rowIterate a stride plan c n v (k+1) result) 1 0 B
      ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩ (by omega)
    have hcb : cw≤2^30*(B+6)^2 := by
      apply hcw.trans
      simpa only [show (1:ℕ).bits.length=1 from rfl,show (0:ℕ).bits.length=0 from rfl,
        Nat.add_zero,show B+1+5=B+6 by omega] using hcw'
    unfold rowMapStepCost rowFoldStepCost
    omega
  obtain ⟨cost,t,finalWord,ex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin
    (.seq (rowPlanCode stride plan) (.seq c.code (rowWriteCode 1 0 result))) input tape xs.length inv
    (fun _ => rowMapStepCost stride O B plan c) stable step n xs s hn hcount rfl
    ⟨le_rfl,by simpa only [Nat.sub_self,rowIterate] using hs,ha,
      by simpa only [Nat.sub_self,Table.filled_initial] using hb,hblank⟩
  exact ⟨cost,t,finalWord,ex,by simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost,
    by simpa only [Nat.sub_zero] using hfinal.2.1,hfinal.2.2.1,hfinal.2.2.2.1,hfinal.2.2.2.2,hword,hl⟩

#print axioms rowMap_executes
end Maxwell.Continuum.RationalDataflow.PartArray
