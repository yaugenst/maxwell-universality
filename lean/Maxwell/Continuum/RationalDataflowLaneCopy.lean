import Maxwell.Continuum.RationalDataflowRowWritePlan
import Maxwell.Continuum.RationalDataflowSharedMapState

/-! A fixed runtime traversal copies a source table into one lane of a
larger table. Reads, address arithmetic, writes, and countdowns are charged. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def laneCopyBody (stride offset entry : ℕ) : Code :=
  .seq (rowPlanCode 1 [(0,entry)]) (rowWriteCode stride offset entry)

def laneCopyCode (stride offset entry : ℕ) : Code := countedProgram 201 (laneCopyBody stride offset entry)

def laneCopyValues {n : ℕ} (a : Table n) (entry : ℕ) (v : ℕ→Parts) : ℕ→(ℕ→Parts)
  | 0 => v
  | k+1 => Function.update (laneCopyValues a entry v k) entry (a.getD (n-1-k))

def laneCopyTable {n m : ℕ} (a : Table n) (b : Table m) (stride offset : ℕ) : ℕ→Table m
  | 0 => b
  | k+1 => (laneCopyTable a b stride offset k).setD (stride*(n-1-k)+offset) (a.getD (n-1-k))

theorem laneCopyTable_metadata {n m : ℕ} (a : Table n) (b : Table m) (stride offset k : ℕ) :
    (laneCopyTable a b stride offset k).width=b.width ∧
    (laneCopyTable a b stride offset k).basePositive=b.basePositive ∧
    (laneCopyTable a b stride offset k).baseNegative=b.baseNegative ∧
    (laneCopyTable a b stride offset k).baseDenominator=b.baseDenominator ∧
    (laneCopyTable a b stride offset k).clock=b.clock := by
  induction k with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | succ k ih =>
    dsimp only [laneCopyTable]
    unfold Table.setD
    split_ifs <;> exact ih

theorem laneCopy_executes {n m : ℕ} (a : Table n) (b : Table m) (stride offset entry : ℕ)
    (S : Finset ℕ) (he : entry∈S) (B : ℕ) (hB : 0<B)
    (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hslot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hindex : ∀r<n,stride*r+offset<m) (v : ℕ→Parts) (hv : WidthBank S B v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t finalWord, Executes input tape (laneCopyCode stride offset entry) cost s t ∧
      cost≤(n+1)*(13*xs.length+15)+n*(2^32*(B+stride.bits.length+offset.bits.length+6)^2) ∧
      RationalDataflow.Ready S (laneCopyValues a entry v n) t ∧
      WidthBank S B (laneCopyValues a entry v n) ∧ a.Ready t ∧
      (laneCopyTable a b stride offset n).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤n ∧
    RationalDataflow.Ready S (laneCopyValues a entry v (n-remaining)) st ∧
    WidthBank S B (laneCopyValues a entry v (n-remaining)) ∧ a.Ready st ∧
    (laneCopyTable a b stride offset (n-remaining)).OutputReady st ∧
    (∀i∈RowIndex.ids,RationalAccumulator.Blank st.val i)
  have stable : ∀r s t,CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t f hh
    refine ⟨hh.1,RationalDataflow.Ready.count_frame _ _ _ (outside_workspace _ _ (by decide))
      hh.2.1 f,hh.2.2.1,hh.2.2.2.1.count_frame f,hh.2.2.2.2.1.count_frame f,?_⟩
    intro i hi
    apply RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i _) (hh.2.2.2.2.2 i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have step : ∀r ys st,inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost t,Executes input tape (laneCopyBody stride offset entry) cost st t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧
        cost≤2^32*(B+stride.bits.length+offset.bits.length+6)^2 := by
    intro r ys st hh hword hvalue hlength
    have hr : r<n := by have := hh.1;omega
    let k := n-(r+1)
    have hk : n-1-k=r := by dsimp [k];omega
    have hnext : k+1=n-r := by dsimp [k];omega
    obtain ⟨cr,s1,er,hcr,r1,w1,a1,z1,f1⟩ := rowPlan_executes a S 1 0 B [(0,entry)]
      (by simpa using he) (by simp) haMeta (laneCopyValues a entry v k) hh.2.2.1
      input tape ys (by omega) (by simpa only [List.mem_cons,List.not_mem_nil,or_false,
        forall_eq,one_mul,add_zero,hvalue] using hr) st hh.2.1 hh.2.2.2.1 ⟨origin,hword⟩ hh.2.2.2.2.2
    have r1' : RationalDataflow.Ready S (laneCopyValues a entry v (k+1)) s1 := by
      simpa only [rowPlanValues,one_mul,add_zero,hvalue,laneCopyValues,hk] using r1
    have w1' : WidthBank S B (laneCopyValues a entry v (k+1)) := by
      simpa only [rowPlanValues,one_mul,add_zero,hvalue,laneCopyValues,hk] using w1
    have b1 := hh.2.2.2.2.1.rowPlan_frame f1 a1.scratch a1.seven
    obtain ⟨mw,mp,mn,md,mc⟩ := laneCopyTable_metadata a b stride offset k
    have hmeta : (laneCopyTable a b stride offset k).MetadataWidth B :=
      ⟨by simpa only [mw] using hbMeta.width,by simpa only [mp] using hbMeta.basePositive,
        by simpa only [mn] using hbMeta.baseNegative,by simpa only [md] using hbMeta.baseDenominator,
        by simpa only [mc] using hbMeta.clock⟩
    have sep : (laneCopyTable a b stride offset k).Separated := by
      simpa only [Table.Separated,mw,mp,mn,md] using hsep
    have disjoint : a.SeparatedFrom (laneCopyTable a b stride offset k) := by
      simpa only [Table.SeparatedFrom,mw,mp,mn,md] using hdisjoint
    have fits : (laneCopyValues a entry v (k+1) entry).Width
        (addressValue (laneCopyTable a b stride offset k).width) := by
      simpa only [mw] using (w1' entry he).mono hslot
    obtain ⟨cw,t,ew,hcw,rt,at',bt,zt,_,fw⟩ := rowWrite_executes a
      (laneCopyTable a b stride offset k) S stride offset entry he (laneCopyValues a entry v (k+1))
      (by simpa only [mw] using lt_of_lt_of_le hB hslot) fits sep disjoint input tape ys
      (by rw [hvalue];exact hindex r hr) s1 r1' a1 b1 ⟨origin,f1.counter.trans hword⟩ z1
    have bt' : (laneCopyTable a b stride offset (n-r)).OutputReady t := by
      rw [←hnext,laneCopyTable,hk]
      simpa only [hvalue,laneCopyValues,Function.update_self,hk,Table.setD,
        dite_eq_left (hindex r hr)] using bt
    have rt' : RationalDataflow.Ready S (laneCopyValues a entry v (n-r)) t := by rwa [hnext] at rt
    have w1'' : WidthBank S B (laneCopyValues a entry v (n-r)) := by rwa [hnext] at w1'
    refine ⟨cr+cw,t,er.seq ew,⟨by omega,rt',w1'',at',bt',zt⟩,
      fw.counter.trans (f1.counter.trans hword),?_⟩
    have hcw' := rowWriteCost_polynomial (laneCopyTable a b stride offset k) ys
      (laneCopyValues a entry v (k+1) entry) stride offset B hmeta (by omega)
    have hread : cr≤2^30*(B+6)^2+1 := by
      simpa only [rowPlanCost,List.length_singleton,Nat.one_mul,
        show (1:ℕ).bits.length=1 from rfl,Nat.add_zero,show B+1+5=B+6 by omega] using hcr
    have hp : (B+6)^2≤(B+stride.bits.length+offset.bits.length+6)^2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hq : (B+stride.bits.length+offset.bits.length+5)^2≤
        (B+stride.bits.length+offset.bits.length+6)^2 := Nat.pow_le_pow_left (by omega) 2
    have hpos : 1≤(B+stride.bits.length+offset.bits.length+6)^2 := by
      simpa only [one_pow] using Nat.pow_le_pow_left
        (by omega : 1≤B+stride.bits.length+offset.bits.length+6) 2
    norm_num at hread hcw' ⊢
    nlinarith only [hread,hcw,hcw',hp,hq,hpos]
  obtain ⟨cost,t,finalWord,hex,hfinal,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin
    (laneCopyBody stride offset entry) input tape xs.length inv
    (fun _ => 2^32*(B+stride.bits.length+offset.bits.length+6)^2) stable step n xs s hn hcount rfl
    ⟨le_rfl,by simpa only [Nat.sub_self,laneCopyValues] using hs,
      by simpa only [Nat.sub_self,laneCopyValues] using hv,ha,
      by simpa only [Nat.sub_self,laneCopyTable] using hb,hblank⟩
  refine ⟨cost,t,finalWord,hex,?_,?_,?_,hfinal.2.2.2.1,?_,hfinal.2.2.2.2.2,hword,hl⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost
  · simpa only [Nat.sub_zero] using hfinal.2.1
  · simpa only [Nat.sub_zero] using hfinal.2.2.1
  · simpa only [Nat.sub_zero] using hfinal.2.2.2.2.1

#print axioms laneCopy_executes
end Maxwell.Continuum.RationalDataflow.PartArray
