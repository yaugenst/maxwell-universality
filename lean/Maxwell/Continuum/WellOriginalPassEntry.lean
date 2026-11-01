import Maxwell.Continuum.WellOriginalPassIncrement

/-! One original strength entry returns to the same canonical rational
bank. Its exact memory write is above the complete saved source prefix. -/
namespace Maxwell.Continuum.RationalDataflow.WellOriginalPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def entryCode : Code := .seq WellOriginalWrite.code WellStrengthReset.code

def entryCost {n J : ℕ} (p : Plan n J) : ℕ :=
  2^22*(p.budget+3)^2+2^184*(p.precision+p.budget+16)^2+2^20*(p.metadataBudget+5)^2+
    (11*operationCost (p.precision+4096*p.budget+4179)+1)

theorem entry_executes {n J i : ℕ} (p : Plan n J) (a : PartArray.Table J) (hi : i<n)
    (memory : ℕ→Bool) (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : State p a i memory s) :
    ∃cost t,Executes input tape entryCode cost s t ∧ cost ≤ entryCost p ∧
      State p (a.set ⟨i,hi.trans_le p.capacity⟩ (p.part ⟨i,hi⟩)) i memory t ∧
      t.val.memory=a.writeMemory ⟨i,hi.trans_le p.capacity⟩ (p.part ⟨i,hi⟩) s.val.memory ∧
      (p.part ⟨i,hi⟩).Width (addressValue a.width) ∧
      (∀k,300 ≤ k→k<1000→k ≠ 995→k ≠ 996→t.val.tapes k=s.val.tapes k) := by
  have fit : p.precision+4096*p.budget+4179 ≤ addressValue a.width := by have := h.fit;omega
  have ibits : i.bits.length ≤ n.bits.length := by
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size hi.le
  have channels := WellStrengthReset.canonical_natural_channels p.values
  rw [p.canonical] at channels
  have readerWidth : ∀k∈WellSourceRead.metaIds,(readerValues k).bits.length ≤ p.budget := by
    intro k _
    have twoBits : (2:ℕ).bits.length=2 := by decide
    simpa only [readerValues,twoBits] using (show 2 ≤ p.budget by have := p.budget_ge;omega)
  obtain ⟨c0,u,e0,hc0,r0,g0,w0,value0,out0,memory0,z0,power0,_,reader0,f0⟩ :=
    WellOriginalWrite.executes a p.diagonalWords p.degreeWords p.diagonalBase p.degreeBase
      p.precision p.budget p.metadataBudget p.budget_ge p.power_width p.diagonalBase_width p.degreeBase_width
      i.bits (ibits.trans p.count_width) ⟨i,hi⟩ (addressValue_bits i) p.values p.width p.good
      channels.1 channels.2.1 channels.2.2.1 channels.2.2.2 p.scale_nonzero (p.denominator_nonzero ⟨i,hi⟩)
      readerValues readerWidth ⟨i,hi.trans_le p.capacity⟩ i.bits (addressValue_bits i)
      (ibits.trans p.outputIndex_width) h.metadata fit h.separated input tape s h.rational h.clean h.power
      h.reader h.diagonalBase h.degreeBase h.sourceIndex h.diagonals h.degrees h.table h.outputIndex
  have parametersWidth : ∀k∈WellStrengthReset.parameters,
      (WellOriginalWrite.output p.precision p.values (addressValue (p.diagonalWords.get ⟨i,hi⟩))
        (addressValue (p.degreeWords.get ⟨i,hi⟩)) k).Width p.budget := by
    intro k hk
    rw [WellStrengthReset.original_parameter _ _ _ _ k hk]
    apply p.width
    simp only [WellStrengthReset.parameters,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl <;> decide
  obtain ⟨c1,t,e1,hc1,r1,_,_,f1⟩ := WellStrengthReset.executes _
    (p.precision+4096*p.budget+4179) p.budget (by omega) (by have := p.budget_ge;omega)
    w0 g0 parametersWidth input tape u r0
  rw [WellStrengthReset.reset_original,p.canonical] at r1
  have out1 := out0.rounded_frame r1 (f1.mono (RoundedInteger.arithmetic_workspace_subset WellStrength.bank))
  change WellOriginalWrite.output p.precision p.values _ _ 0=p.part ⟨i,hi⟩ at value0
  rw [value0] at out1 memory0
  have partWidth : (p.part ⟨i,hi⟩).Width (addressValue a.width) := by
    rw [←value0]
    exact (w0 0 (by decide)).mono fit
  have mem : t.val.memory=a.writeMemory ⟨i,hi.trans_le p.capacity⟩ (p.part ⟨i,hi⟩) s.val.memory :=
    f1.memory.trans memory0
  have keep (k : ℕ) (hk : 300 ≤ k) (hk' : k<1000) (h995 : k ≠ 995) (h996 : k ≠ 996) :
      t.val.tapes k=s.val.tapes k :=
    (f1.tapes k (outside_workspace WellStrength.bank k (Or.inr ⟨by omega,hk'⟩))).trans (f0 k hk hk' h995 h996)
  have above (base : List Bool) (hb : base∈[a.basePositive,a.baseNegative,a.baseDenominator]) :
      p.prefixLimit ≤ addressValue base := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl
    · exact h.above.1
    · exact h.above.2.1
    · exact h.above.2.2
  have diagonals : BitArray.Represents t.val.memory p.diagonalBase 4 p.diagonalWords := by
    rw [mem]
    apply a.writeMemory_preserves _ _ h.diagonals
    intro base hb
    exact Or.inl (p.diagonal_below.trans (above base hb))
  have degrees : BitArray.Represents t.val.memory p.degreeBase 2 p.degreeWords := by
    rw [mem]
    apply a.writeMemory_preserves _ _ h.degrees
    intro base hb
    exact Or.inl (p.degree_below.trans (above base hb))
  have reader : NatAssign.Bank WellSourceRead.metaIds readerValues t.val := by
    intro k hk
    have hout : k∉workspace WellStrength.bank := by
      simp only [WellSourceRead.metaIds,Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl|rfl <;> exact outside_workspace _ _ (by decide)
    have word := word_of_eq (f1.tapes k hout) (reader0 k hk)
    simp only [WellSourceRead.metaIds,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl
    · simpa only [readerValues,WellSourceRead.prepared_width] using word
    · simpa only [readerValues,WellSourceRead.prepared_clock] using word
  have metadata : (a.set ⟨i,hi.trans_le p.capacity⟩ (p.part ⟨i,hi⟩)).MetadataWidth p.metadataBudget :=
    ⟨h.metadata.width,h.metadata.basePositive,h.metadata.baseNegative,h.metadata.baseDenominator,h.metadata.clock⟩
  refine ⟨c0+c1,t,e0.seq e1,by unfold entryCost;omega,
    ⟨r1,z0.arithmetic_frame f1,word_of_eq (f1.tapes 144 (outside_workspace _ _ (by decide))) power0,
      out1,metadata,h.fit,h.separated,h.above,diagonals,degrees,
      word_of_eq (keep 993 (by decide) (by decide) (by decide) (by decide)) h.diagonalBase,
      word_of_eq (keep 994 (by decide) (by decide) (by decide) (by decide)) h.degreeBase,
      word_of_eq (keep 998 (by decide) (by decide) (by decide) (by decide)) h.sourceIndex,
      word_of_eq (keep 999 (by decide) (by decide) (by decide) (by decide)) h.outputIndex,
      reader,word_of_eq (keep 988 (by decide) (by decide) (by decide) (by decide)) h.totalCount,
      word_of_eq (keep 963 (by decide) (by decide) (by decide) (by decide)) h.originalCount,?_⟩,mem,partWidth,keep⟩
  intro k hk
  rw [mem,a.writeMemory_prefix _ _ _ p.prefixLimit h.above.1 h.above.2.1 h.above.2.2 k hk]
  exact h.savedPrefix k hk

#print axioms entry_executes
end Maxwell.Continuum.RationalDataflow.WellOriginalPass
