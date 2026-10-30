import Maxwell.Continuum.RationalDataflowSharedMap
import Maxwell.Continuum.RationalDataflowControlResults

/-! A fixed arithmetic control scans a runtime input table and materializes its
outputs. Every indexed read, arithmetic step, and indexed write is charged. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem workspace_subset_shared (S : Finset ℕ) : workspace S⊆SharedConversion.changed S := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · apply Finset.mem_union_left
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    tauto
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hi)

theorem sharedReady_arithmetic_frame {S : Finset ℕ} {v w : ℕ→Parts} {s t : Store}
    (h : SharedConversion.Ready S v s) (f : BinaryPrecision.Frame (workspace S) s.val t.val)
    (hb : RationalDataflow.Ready S w t) : SharedConversion.Ready S w t := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hb.1 i hi
    · have hout : i∉workspace S := by
        apply outside_workspace S i
        simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
        omega
      have old := h.1 i (Finset.mem_union_right _ hi)
      rw [SharedConversion.work_values_zero v i hi] at old
      rw [SharedConversion.work_values_zero w i hi]
      exact RationalAccumulator.word_of_eq (f.tapes i hout) old
  · intro i hi
    by_cases hlt : i<4
    · exact hb.2 i hlt
    · have he : i=4 := by omega
      subst i
      exact RationalAccumulator.blank_of_eq (f.tapes 4 (outside_workspace S 4 (by decide)))
        (h.2 4 (by decide))

def mapCode (c : Control) (result : ℕ) : Code :=
  countedProgram 201 (.seq (readCode 1) (.seq c.code (writeCode result)))

def mapValues {n : ℕ} (a : Table n) (c : Control) (result : ℕ) (v : ℕ→Parts) : Fin n→Parts :=
  fun i => iterate a 1 c v (n-i.val) result

def mapStepCost (c : Control) (B : ℕ) : ℕ := 2^21*(B+5)^2+c.steps*operationCost B+1

theorem map_executes {n : ℕ} (a b : Table n) (S : Finset ℕ) (h1 : 1∈S)
    (c : Control) (hc : c.Valid S) (result : ℕ) (hr : result∈S) (v : ℕ→Parts)
    (B : ℕ) (hB : 0<B) (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hslot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hw : ∀ k<n, WidthBank S B (iterate a 1 c v k))
    (htrace : ∀ k<n, c.WidthTrace S B (loaded a 1 c v k))
    (hg : ∀ k<n, Good S (loaded a 1 c v k))
    (had : ∀ k<n, c.AdmissibleTrace (loaded a 1 c v k))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : SharedConversion.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s) :
    ∃ cost t finalWord, Executes input tape (mapCode c result) cost s t ∧
      cost≤(n+1)*(13*xs.length+15)+n*mapStepCost c B ∧
      SharedConversion.Ready S (iterate a 1 c v n) t ∧ a.Ready t ∧
      (b.filled (mapValues a c result v) 0).OutputReady t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  let value := mapValues a c result v
  let inv : ℕ→Store→Prop := fun remaining st =>
    remaining≤n ∧ SharedConversion.Ready S (iterate a 1 c v (n-remaining)) st ∧
      a.Ready st ∧ (b.filled value remaining).OutputReady st
  have stable : ∀ r s t, CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t f hh
    exact ⟨hh.1,sharedReady_count_frame hh.2.1 f,hh.2.2.1.count_frame f,hh.2.2.2.count_frame f⟩
  have step : ∀ r ys st, inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost out, Executes input tape (.seq (readCode 1) (.seq c.code (writeCode result))) cost st out ∧
        inv r out ∧ out.val.tapes 201=BitTape.shifted ys origin ∧ cost≤mapStepCost c B := by
    intro r ys st hh hword hvalue hlength
    have hrn : r<n := by have := hh.1; omega
    let k := n-(r+1)
    have hk : k<n := by dsimp [k]; omega
    have hindex : n-1-k=r := by dsimp [k]; omega
    have hnext : k+1=n-r := by dsimp [k]; omega
    have hget : a.getD (n-1-k)=a.get ⟨r,hrn⟩ := by simp only [hindex,Table.getD,dite_eq_left hrn]
    obtain ⟨cr,t1,er,hcr,r1,a1,_,f1⟩ := read_executes a S 1 h1
      (iterate a 1 c v k) input tape ys ⟨r,hrn⟩ hvalue st hh.2.1.rational hh.2.2.1 ⟨origin,hword⟩
    have r1' : RationalDataflow.Ready S (loaded a 1 c v k) t1 := by
      simpa only [loaded,hget] using r1
    have e1 := sharedReady_read_frame hh.2.1 f1 (er.protectsTape 4 read_one_protects_four) r1'
    have b1 := hh.2.2.2.read_frame f1 a1.scratch a1.seven
    obtain ⟨cc,t2,ec,hcc,r2,f2⟩ := c.executes S hc _ B (htrace k hk) (hg k hk)
      (had k hk) input tape t1 r1'
    have e2 : SharedConversion.Ready S (iterate a 1 c v (k+1)) t2 :=
      sharedReady_arithmetic_frame e1 f2 r2
    have a2 := a1.arithmetic_frame S f2 r2.2
    have b2 := b1.shared_frame S (f2.mono (workspace_subset_shared S)) a2.scratch a2.seven
    have fit : (iterate a 1 c v (k+1) result).Width (addressValue b.width) :=
      ((htrace k hk).result result hr).mono hslot
    have index1 : t1.val.tapes 201=BitTape.shifted ys origin :=
      (f1.tapes 201 (by decide) (by decide)).trans hword
    have index2 : t2.val.tapes 201=BitTape.shifted ys origin :=
      (f2.tapes 201 (outside_workspace S 201 (by decide))).trans index1
    obtain ⟨cw,t3,ew,hcw,e3,b3,m3,f3⟩ := write_executes (b.filled value (r+1)) S result hr
      (iterate a 1 c v (k+1)) ⟨r,hrn⟩ (lt_of_lt_of_le hB hslot) fit hsep
      input tape ys hvalue t2 e2 b2 ⟨origin,index2⟩
    have a3 := a2.write_output_frame hdisjoint ⟨r,hrn⟩ (iterate a 1 c v (k+1) result)
      m3 f3 b3.scratch b3.seven
    have output : iterate a 1 c v (k+1) result=value ⟨r,hrn⟩ := by
      change iterate a 1 c v (k+1) result=iterate a 1 c v (n-r) result
      rw [hnext]
    have b3' : (b.filled value r).OutputReady t3 := by
      rw [output,Table.filled_step] at b3
      exact b3
    have e3' : SharedConversion.Ready S (iterate a 1 c v (n-r)) t3 := by rwa [hnext] at e3
    refine ⟨cr+(cc+cw),t3,er.seq (ec.seq ew),⟨by omega,e3',a3,b3'⟩,
      (f3.2.2.2.1 201 (Or.inr (by decide)) (by decide)).trans index2,?_⟩
    have readBound := a.readCost_bound B haMeta ys (by omega) _ (hw k hk 1 h1)
    change cw≤(b.filled value (r+1)).writeCost ys (iterate a 1 c v (k+1) result) at hcw
    have writeBound := (b.filled value (r+1)).writeCost_bound B
      ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩
      ys (by omega) (iterate a 1 c v (k+1) result)
    unfold mapStepCost
    nlinarith only [hcr,readBound,hcc,hcw,writeBound]
  have initial : inv n s := by
    refine ⟨le_rfl,?_,ha,?_⟩
    · simpa only [Nat.sub_self,iterate] using hs
    · simpa only [Table.filled_initial] using hb
  obtain ⟨cost,t,finalWord,hex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin
    (.seq (readCode 1) (.seq c.code (writeCode result))) input tape xs.length inv
    (fun _ => mapStepCost c B) stable step n xs s hn hcount rfl initial
  refine ⟨cost,t,finalWord,hex,?_,?_,hfinal.2.2.1,hfinal.2.2.2,hword,hl⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost
  · simpa only [Nat.sub_zero] using hfinal.2.1

#print axioms map_executes
end Maxwell.Continuum.RationalDataflow.PartArray
