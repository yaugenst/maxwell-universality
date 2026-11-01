import Maxwell.Continuum.WellStrengthReset
import Maxwell.Continuum.RationalDataflowArrayWritePrefix
import Maxwell.Continuum.RationalDataflowCounted
import Maxwell.Cost.PhysicalEmit.Increment

/-! Computational data and a reusable loop invariant for the original
strength pass. The source words and all cursor values are represented by
the machine; physical identities are established separately. -/
namespace Maxwell.Continuum.RationalDataflow.WellOriginalPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

structure Plan (n J : ℕ) where
  diagonalWords : Vector (List Bool) n
  degreeWords : Vector (List Bool) n
  diagonalBase : ℕ
  degreeBase : ℕ
  precision : ℕ
  budget : ℕ
  metadataBudget : ℕ
  prefixLimit : ℕ
  values : ℕ→Parts
  canonical : WellStrengthReset.canonical values=values
  width : WidthBank WellStrength.bank budget values
  good : Good WellStrength.bank values
  budget_ge : 4 ≤ budget
  power_width : (2^precision).bits.length ≤ budget
  diagonalBase_width : diagonalBase.bits.length ≤ budget
  degreeBase_width : degreeBase.bits.length ≤ budget
  count_width : n.bits.length ≤ budget
  outputIndex_width : n.bits.length ≤ metadataBudget
  capacity : n ≤ J
  diagonal_below : diagonalBase+n*4 ≤ prefixLimit
  degree_below : degreeBase+n*2 ≤ prefixLimit
  scale_nonzero : (values 4).value ≠ 0
  denominator_nonzero : ∀i:Fin n,(values 1).value+
    WellOriginalWrite.target values (addressValue (diagonalWords.get i)) (addressValue (degreeWords.get i)) ≠ 0

def Plan.part {n J : ℕ} (p : Plan n J) (i : Fin n) : Parts :=
  Parts.literal (WellStrength.numerator p.precision (p.values 1).value
    (WellOriginalWrite.target p.values (addressValue (p.diagonalWords.get i))
      (addressValue (p.degreeWords.get i))):ℚ)

def readerValues : ℕ→ℕ := fun _=>2

structure State {n J : ℕ} (p : Plan n J) (a : PartArray.Table J) (index : ℕ)
    (memory : ℕ→Bool) (s : Store) : Prop where
  rational : Ready WellStrength.bank p.values s
  clean : DyadicFloor.Clean s.val
  power : Word s.val 144 (2^p.precision)
  table : a.OutputReady s
  metadata : a.MetadataWidth p.metadataBudget
  fit : p.precision+4096*(256*(p.budget+1))+4179 ≤ addressValue a.width
  separated : a.Separated
  above : p.prefixLimit ≤ addressValue a.basePositive ∧ p.prefixLimit ≤ addressValue a.baseNegative ∧
    p.prefixLimit ≤ addressValue a.baseDenominator
  diagonals : BitArray.Represents s.val.memory p.diagonalBase 4 p.diagonalWords
  degrees : BitArray.Represents s.val.memory p.degreeBase 2 p.degreeWords
  diagonalBase : Word s.val 993 p.diagonalBase
  degreeBase : Word s.val 994 p.degreeBase
  sourceIndex : Word s.val 998 index
  outputIndex : Word s.val 999 index
  reader : NatAssign.Bank WellSourceRead.metaIds readerValues s.val
  totalCount : Word s.val 988 J
  originalCount : Word s.val 963 n
  savedPrefix : ∀j,j<p.prefixLimit→s.val.memory j=memory j

def external : Finset ℕ := {972,998,999}

theorem external_outside (i : ℕ) (hi : i∈external) : i∉workspace WellStrength.bank := by
  apply outside_workspace
  simp only [external,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem State.external_frame {n J i j : ℕ} {p : Plan n J} {a : PartArray.Table J}
    {memory : ℕ→Bool} {s t : Store} (h : State p a i memory s)
    (f : BinaryPrecision.Frame external s.val t.val)
    (hsource : Word t.val 998 j) (houtput : Word t.val 999 j) : State p a j memory t := by
  have keep (k : ℕ) (hk : k∉external) := f.tapes k hk
  have ready : Ready WellStrength.bank p.values t := by
    constructor
    · intro k hk
      have hout : k∉external := fun he=>external_outside k he (Finset.mem_union_right _ hk)
      exact word_of_eq (keep k hout) (h.rational.1 k hk)
    · intro k hk
      exact blank_of_eq (keep k (by simp [external];omega)) (h.rational.2 k hk)
  have scratch : BankArray.Scratch t.val :=
    ⟨blank_of_eq (keep 0 (by decide)) h.table.scratch.1,
      blank_of_eq (keep 1 (by decide)) h.table.scratch.2.1,
      blank_of_eq (keep 2 (by decide)) h.table.scratch.2.2.1,
      blank_of_eq (keep 3 (by decide)) h.table.scratch.2.2.2.1,
      blank_of_eq (keep 5 (by decide)) h.table.scratch.2.2.2.2.1,
      blank_of_eq (keep 6 (by decide)) h.table.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by decide)) h.table.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9 (by decide)) h.table.scratch.2.2.2.2.2.2.2⟩
  have out : a.OutputReady t := by
    apply h.table.transfer f.memory _ scratch (blank_of_eq (keep 7 (by decide)) h.table.seven)
    intro k hk
    apply keep
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have clean : DyadicFloor.Clean t.val := by
    refine ⟨blank_of_eq (keep 4 (by decide)) h.clean.1,?_⟩
    intro k hk
    have hout : k∉external := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [external,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact blank_of_eq (keep k hout) (h.clean.2 k hk)
  refine ⟨ready,clean,word_of_eq (keep 144 (by decide)) h.power,out,h.metadata,h.fit,h.separated,h.above,
    ?_,?_,word_of_eq (keep 993 (by decide)) h.diagonalBase,word_of_eq (keep 994 (by decide)) h.degreeBase,
    hsource,houtput,?_,word_of_eq (keep 988 (by decide)) h.totalCount,
    word_of_eq (keep 963 (by decide)) h.originalCount,?_⟩
  · simpa only [f.memory] using h.diagonals
  · simpa only [f.memory] using h.degrees
  · intro k hk
    have hout : k∉external := by
      simp only [WellSourceRead.metaIds,Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl|rfl <;> decide
    exact word_of_eq (keep k hout) (h.reader k hk)
  · intro k hk
    rw [f.memory]
    exact h.savedPrefix k hk

theorem State.count_frame {n J i : ℕ} {p : Plan n J} {a : PartArray.Table J}
    {memory : ℕ→Bool} {s t : Store} (h : State p a i memory s) (f : CountedShifted.Frame 972 s t) :
    State p a i memory t := by
  have frame : BinaryPrecision.Frame external s.val t.val :=
    ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,fun k hk=>f.2.2.2.2.2.1 k (by
      simp only [external,Finset.mem_insert,Finset.mem_singleton,not_or] at hk;omega)⟩
  exact h.external_frame frame
    (word_of_eq (f.2.2.2.2.2.1 998 (by decide)) h.sourceIndex)
    (word_of_eq (f.2.2.2.2.2.1 999 (by decide)) h.outputIndex)

#print axioms State.external_frame
end Maxwell.Continuum.RationalDataflow.WellOriginalPass
