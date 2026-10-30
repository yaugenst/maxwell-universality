import Maxwell.Continuum.CutoffMonomialSeedValues
import Maxwell.Continuum.RationalDataflowArrayMap

/-! Actual initialization of the cached Chebyshev buffer, including every
zero channel and the two nonzero unit coefficients. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def monomialSeedPlan : List (ℕ×ℕ) := [(4,0),(9,0)]
def monomialSeedCode : Code :=
  .seq (NatAssign.code (literalStage 0 (Parts.literal 0)))
    (.seq (fillCode 0) (.seq (NatAssign.code (literalStage 0 (Parts.literal 1)))
      (rowWritePlanCode 0 monomialSeedPlan)))

def monomialSeedCost (D B len : ℕ) : ℕ := 2*stageCost B+
  (4*(D+1)+1)*(13*len+15)+4*(D+1)*(2^30*(B+6)^2)+rowPlanCost 0 4 B monomialSeedPlan

theorem monomialSeed_executes {n D : ℕ} (a : Table n) (b : Table (4*(D+1))) (hD : 2≤D)
    (B : ℕ) (hB : 1≤B) (hbMeta : b.MetadataWidth B) (hslot : B≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b) (S : Finset ℕ) (h0 : 0∈S)
    (v : ℕ→Parts) (hv : WidthBank S B v) (input : List Bool) (tape : ℕ→Bool)
    (xs : List Bool) (origin : ℤ) (hlen : xs.length≤B) (s : Store)
    (hn : addressValue xs=4*(D+1)) (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t finalWord, Executes input tape monomialSeedCode cost s t ∧
      cost≤monomialSeedCost D B xs.length ∧
      RationalDataflow.Ready S (Function.update v 0 (Parts.literal 1)) t ∧ a.Ready t ∧
      (monomialSeedTable b).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  have hz : (Parts.literal 0).Width B := (Parts.literal_width RationalWords.width_zero').mono hB
  have ho : (Parts.literal 1).Width B := (Parts.literal_width RationalWords.width_one).mono hB
  obtain ⟨c0,s0,e0,hc0,r0,f0⟩ := literal_executes S 0 h0 (Parts.literal 0) v B hz hv input tape s hs
  have a0 := ha.arithmetic_frame S f0 r0.2
  have b0 := hb.shared_frame S (f0.mono (workspace_subset_shared S)) a0.scratch a0.seven
  have z0 : ∀i∈RowIndex.ids,RationalAccumulator.Blank s0.val i := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f0.tapes i _) (hblank i hi)
    apply outside_workspace S i
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have count0 := (f0.tapes 201 (outside_workspace _ _ (by decide))).trans hcount
  obtain ⟨cf,s1,finalWord,ef,hcf,r1,a1,b1,z1,count1,length1⟩ := fill_executes a b S 0 h0
    (Function.update v 0 (Parts.literal 0)) B hbMeta (by omega) (by simpa using hz.mono hslot)
    hsep hdisjoint input tape xs origin hlen s0 hn count0 r0 a0 b0 z0
  have b1' : (b.filled (fun _ => Parts.literal 0) 0).OutputReady s1 := by
    simpa only [Function.update_self] using b1
  obtain ⟨c1,s2,e1,hc1,r2,f1⟩ := literal_executes S 0 h0 (Parts.literal 1)
    (Function.update v 0 (Parts.literal 0)) B ho (hv.update 0 hz) input tape s1 r1
  have a2 := a1.arithmetic_frame S f1 r2.2
  have b2 := b1'.shared_frame S (f1.mono (workspace_subset_shared S)) a2.scratch a2.seven
  have r2' : RationalDataflow.Ready S (Function.update v 0 (Parts.literal 1)) s2 := by
    simpa only [Function.update_idem] using r2
  have z2 : ∀i∈RowIndex.ids,RationalAccumulator.Blank s2.val i := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f1.tapes i _) (z1 i hi)
    apply outside_workspace S i
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have count2 := (f1.tapes 201 (outside_workspace _ _ (by decide))).trans count1
  have hp : ∀x∈monomialSeedPlan,x.2∈S := by simpa [monomialSeedPlan] using h0
  have hindex : ∀x∈monomialSeedPlan,0*addressValue finalWord+x.1<4*(D+1) := by
    intro x hx
    simp only [monomialSeedPlan,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> simp only [Nat.zero_mul,Nat.zero_add] <;> omega
  have hfits : ∀x∈monomialSeedPlan,((Function.update v 0 (Parts.literal 1)) x.2).Width
      (addressValue (b.filled (fun _ => Parts.literal 0) 0).width) := by
    intro x hx
    simp only [monomialSeedPlan,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> exact ho.mono hslot
  obtain ⟨cw,t,ew,hcw,rt,at',bt,zt,ft⟩ := rowWritePlan_executes a (b.filled (fun _ => Parts.literal 0) 0)
    S 0 4 B monomialSeedPlan hp (by decide)
    ⟨hbMeta.width,hbMeta.basePositive,hbMeta.baseNegative,hbMeta.baseDenominator,hbMeta.clock⟩
    (Function.update v 0 (Parts.literal 1)) hfits (by change 0<addressValue b.width;omega)
    hsep hdisjoint input tape finalWord (by omega) hindex s2 r2' a2 b2 ⟨origin,count2⟩ z2
  refine ⟨c0+(cf+(c1+cw)),t,finalWord,e0.seq (ef.seq (e1.seq ew)),?_,rt,at',?_,zt,
    ft.counter.trans count2,length1⟩
  · unfold monomialSeedCost
    omega
  · simpa only [monomialSeedTable,monomialSeedPlan,rowWriteTable,Nat.zero_mul,Nat.zero_add,
      Function.update_self] using bt

#print axioms monomialSeed_executes
end Maxwell.Continuum.Calibration.RawCutoff
