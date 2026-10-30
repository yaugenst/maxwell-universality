import Maxwell.Continuum.ProfileRoundedStore

/-! Invariants for the actual profile output table. Previously stored rows
carry their exact computed values; unread output memory is unrestricted. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def tableMetadata {n : ℕ} (a b : PartArray.Table n) : Prop :=
  b.width=a.width ∧ b.basePositive=a.basePositive ∧ b.baseNegative=a.baseNegative ∧
    b.baseDenominator=a.baseDenominator ∧ b.clock=a.clock

theorem tableMetadata_refl {n : ℕ} (a : PartArray.Table n) : tableMetadata a a := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem tableMetadata_width {n : ℕ} {a b : PartArray.Table n} (h : tableMetadata a b)
    {M : ℕ} (hm : a.MetadataWidth M) : b.MetadataWidth M :=
  ⟨h.1 ▸ hm.width,h.2.1 ▸ hm.basePositive,h.2.2.1 ▸ hm.baseNegative,
    h.2.2.2.1 ▸ hm.baseDenominator,h.2.2.2.2 ▸ hm.clock⟩

theorem tableMetadata_separated {n : ℕ} {a b : PartArray.Table n} (h : tableMetadata a b)
    (hs : a.Separated) : b.Separated := by
  simpa only [PartArray.Table.Separated,h.1,h.2.1,h.2.2.1,h.2.2.2.1] using hs

def roundedTarget (grid D P j : ℕ) : ℚ := (DyadicFloor.result P (sampledParts grid D P j)).value

structure ProducerState (grid D P U : ℕ) (s : Store) where
  values : ℕ→Parts
  ready : Ready dftRegisters values s
  width : WidthBank dftRegisters (roundedWidth grid U) values
  saved : Parts
  stored : StoredParts.Stored 701 saved s.val
  savedWidth : saved.Width (roundedWidth grid U)
  innerWord : List Bool
  innerCounter : BankArray.Word s.val 201 innerWord
  innerLength : innerWord.length≤roundedWidth grid U
  phaseClean : Phase.Runtime.Clean s.val
  glueClean : Glue.Clean s.val
  floorClean : DyadicFloor.Clean s.val
  parameters : DFTParameters D P s
  power : Word s.val 144 (2^P)
  gridWord : Word s.val 664 grid

structure RoundedTableState (grid D P U : ℕ) (a : PartArray.Table D) (remaining : ℕ) (s : Store)
    extends ProducerState grid D P U s where
  bound : remaining≤D
  table : PartArray.Table D
  metadata : tableMetadata a table
  output : table.OutputReady s
  correct : ∀i:Fin D,remaining ≤ i.val → (table.get i).Valid ∧ (table.get i).denominator=1 ∧
    (table.get i).value=roundedTarget grid D P i.val

def ProducerState.count_frame {grid D P U : ℕ} {s t : Store} (h : ProducerState grid D P U s)
    (f : CountedShifted.Frame 700 s t) : ProducerState grid D P U t := by
  have keep (i : ℕ) (hi : i≠700) := f.2.2.2.2.2.1 i hi
  refine ⟨h.values,h.ready.count_frame _ _ _ (RationalDataflow.outside_workspace _ _ (by decide)) f,
    h.width,h.saved,?_,h.savedWidth,h.innerWord,BankArray.word_of_eq (keep 201 (by decide)) h.innerCounter,
    h.innerLength,?_,?_,?_,?_,word_of_eq (keep 144 (by decide)) h.power,
    word_of_eq (keep 664 (by decide)) h.gridWord⟩
  · exact ⟨word_of_eq (keep 701 (by decide)) h.stored.1,
      word_of_eq (keep 702 (by decide)) h.stored.2.1,word_of_eq (keep 703 (by decide)) h.stored.2.2⟩
  · intro i hi
    apply blank_of_eq (keep i _) (h.phaseClean i hi)
    intro he;subst i
    exact (show (700:ℕ)∉PhaseMachine.Runtime.ids by decide)
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
  · intro i hi
    apply blank_of_eq (keep i _) (h.glueClean i hi)
    intro he;subst i
    exact (show (700:ℕ)∉GlueMachine.Runtime.ids by decide) (Finset.mem_of_mem_erase hi)
  · refine ⟨blank_of_eq (keep 4 (by decide)) h.floorClean.1,?_⟩
    intro i hi
    apply blank_of_eq (keep i _) (h.floorClean.2 i hi)
    simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  · exact ⟨word_of_eq (keep 663 (by decide)) h.parameters.precision,
      word_of_eq (keep 667 (by decide)) h.parameters.one,word_of_eq (keep 668 (by decide)) h.parameters.guard,
      word_of_eq (keep 669 (by decide)) h.parameters.range,word_of_eq (keep 652 (by decide)) h.parameters.phaseRange,
      word_of_eq (keep 653 (by decide)) h.parameters.phasePrecision,
      word_of_eq (keep 640 (by decide)) h.parameters.gluePrecision⟩

theorem outputReady_count700 {n : ℕ} {a : PartArray.Table n} {s t : Store} (h : a.OutputReady s)
    (f : CountedShifted.Frame 700 s t) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i≠700) := f.2.2.2.2.2.1 i hi
  have hz : BankArray.Scratch t.val := by
    rcases h.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨blank_of_eq (keep 0 (by decide)) h0,blank_of_eq (keep 1 (by decide)) h1,
      blank_of_eq (keep 2 (by decide)) h2,blank_of_eq (keep 3 (by decide)) h3,
      blank_of_eq (keep 5 (by decide)) h5,blank_of_eq (keep 6 (by decide)) h6,
      blank_of_eq (keep 8 (by decide)) h8,blank_of_eq (keep 9 (by decide)) h9⟩
  apply h.transfer f.2.2.1 _ hz (blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

def RoundedTableState.count_frame {grid D P U : ℕ} {a : PartArray.Table D} {r : ℕ} {s t : Store}
    (h : RoundedTableState grid D P U a r s) (f : CountedShifted.Frame 700 s t) :
    RoundedTableState grid D P U a r t :=
  ⟨h.toProducerState.count_frame f,h.bound,h.table,h.metadata,outputReady_count700 h.output f,h.correct⟩

#print axioms RoundedTableState.count_frame
end Maxwell.Continuum.Profile.Runtime
