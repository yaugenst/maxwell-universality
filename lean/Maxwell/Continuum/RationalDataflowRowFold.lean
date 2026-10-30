import Maxwell.Continuum.RationalDataflowRowPlan

/-! A fixed row-read plan followed by a fixed arithmetic body traverses a
runtime array. Every address calculation, read, and countdown is charged. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def rowIterate {m : ℕ} (a : Table m) (stride : ℕ) (plan : List (ℕ×ℕ))
    (c : Control) (n : ℕ) (v : ℕ→Parts) : ℕ→(ℕ→Parts)
  | 0 => v
  | k+1 => c.evaluate (rowPlanValues a stride (n-1-k) plan (rowIterate a stride plan c n v k))

def rowLoaded {m : ℕ} (a : Table m) (stride : ℕ) (plan : List (ℕ×ℕ))
    (c : Control) (n : ℕ) (v : ℕ→Parts) (k : ℕ) : ℕ→Parts :=
  rowPlanValues a stride (n-1-k) plan (rowIterate a stride plan c n v k)

def rowFoldCode (stride : ℕ) (plan : List (ℕ×ℕ)) (c : Control) : Code :=
  countedProgram 201 (.seq (rowPlanCode stride plan) c.code)

def rowFoldStepCost (stride O B : ℕ) (plan : List (ℕ×ℕ)) (c : Control) : ℕ :=
  rowPlanCost stride O B plan+c.steps*operationCost B+1

theorem rowFold_executes {m : ℕ} (a : Table m) (S : Finset ℕ)
    (stride O : ℕ) (plan : List (ℕ×ℕ)) (hp : ∀x∈plan,x.2∈S)
    (ho : ∀x∈plan,x.1.bits.length≤O) (c : Control) (hc : c.Valid S)
    (n : ℕ) (v : ℕ→Parts) (B : ℕ) (hm : a.MetadataWidth B)
    (hw : ∀k<n,WidthBank S B (rowIterate a stride plan c n v k))
    (ht : ∀k<n,c.WidthTrace S B (rowLoaded a stride plan c n v k))
    (hg : ∀k<n,Good S (rowLoaded a stride plan c n v k))
    (had : ∀k<n,c.AdmissibleTrace (rowLoaded a stride plan c n v k))
    (hix : ∀k<n,∀x∈plan,stride*(n-1-k)+x.1<m)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t finalWord, Executes input tape (rowFoldCode stride plan c) cost s t ∧
      RationalDataflow.Ready S (rowIterate a stride plan c n v n) t ∧ a.Ready t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      cost≤(n+1)*(13*xs.length+15)+n*rowFoldStepCost stride O B plan c := by
  have hout : 201∉workspace S := outside_workspace S 201 (by decide)
  let inv : ℕ→Store→Prop := fun remaining st =>
    remaining≤n ∧ RationalDataflow.Ready S (rowIterate a stride plan c n v (n-remaining)) st ∧
      a.Ready st ∧ (∀i∈RowIndex.ids,RationalAccumulator.Blank st.val i)
  have stable : ∀r s t,CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t f hh
    refine ⟨hh.1,RationalDataflow.Ready.count_frame S _ 201 hout hh.2.1 f,
      hh.2.2.1.count_frame f,?_⟩
    intro i hi
    apply RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i _) (hh.2.2.2 i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have step : ∀r ys s,inv (r+1) s → s.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost t,Executes input tape (.seq (rowPlanCode stride plan) c.code) cost s t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧ cost≤rowFoldStepCost stride O B plan c := by
    intro r ys s hh hword hvalue hlength
    have hr : r<n := by have := hh.1;omega
    let k := n-(r+1)
    have hk : k<n := by dsimp [k];omega
    have hindex : n-1-k=r := by dsimp [k];omega
    obtain ⟨cr,t1,er,hcr,b1,_,a1,z1,f1⟩ := rowPlan_executes a S stride O B plan hp ho hm
      (rowIterate a stride plan c n v k) (hw k hk) input tape ys (by omega)
      (fun x hx => by rw [hvalue,←hindex];exact hix k hk x hx)
      s hh.2.1 hh.2.2.1 ⟨origin,hword⟩ hh.2.2.2
    have b1' : RationalDataflow.Ready S (rowLoaded a stride plan c n v k) t1 := by
      simpa only [rowLoaded,hvalue,hindex] using b1
    obtain ⟨ca,t2,ea,hca,b2,f2⟩ := c.executes S hc _ B (ht k hk) (hg k hk)
      (had k hk) input tape t1 b1'
    have heq : k+1=n-r := by dsimp [k];omega
    have b2' : RationalDataflow.Ready S (rowIterate a stride plan c n v (n-r)) t2 := by
      rw [←heq]
      exact b2
    have z2 : ∀i∈RowIndex.ids,RationalAccumulator.Blank t2.val i := by
      intro i hi
      apply RationalAccumulator.blank_of_eq (f2.tapes i _) (z1 i hi)
      apply outside_workspace S i
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    refine ⟨cr+ca,t2,er.seq ea,⟨by omega,b2',a1.arithmetic_frame S f2 b2.2,z2⟩,
      (f2.tapes 201 hout).trans (f1.counter.trans hword),?_⟩
    unfold rowFoldStepCost
    omega
  obtain ⟨cost,t,finalWord,he,hh,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin
    (.seq (rowPlanCode stride plan) c.code) input tape xs.length inv
    (fun _ => rowFoldStepCost stride O B plan c) stable step n xs s hn hcount rfl
    ⟨le_rfl,by simpa only [Nat.sub_self,rowIterate] using hs,ha,hblank⟩
  refine ⟨cost,t,finalWord,he,?_,hh.2.2.1,hh.2.2.2,hword,hl,?_⟩
  · simpa only [Nat.sub_zero] using hh.2.1
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost

#print axioms rowFold_executes
end Maxwell.Continuum.RationalDataflow.PartArray
