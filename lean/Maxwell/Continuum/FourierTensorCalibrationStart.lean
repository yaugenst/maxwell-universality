import Maxwell.Continuum.FourierTensorCalibrationInput

/-! Prepare the Fourier component compiler from an already produced
calibration array and seven stored runtime parameters. Every required
scratch word is cleared by charged execution; material payloads survive. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationStart
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def parameters : Finset ℕ := {350,351,352,354,355,710,711}
def parameterValues (M A L R P Q N i : ℕ) : ℕ :=
  if i=350 then M else if i=351 then A else if i=352 then L else if i=354 then R
  else if i=355 then P else if i=710 then Q else if i=711 then N else 0

def clearSet : Finset ℕ := (ModeAllocation.ids\ModeAllocation.inputs)∪
  (setupIds\{710,711})∪RationalRoot.ids∪({4}∪DyadicFloor.extraIds∪NaturalQuotient.workPorts)∪
  ((PhaseMachine.Runtime.ids.erase 652).erase 653)∪TensorStart.freshPorts
def clearPorts : List ℕ := clearSet.sort (·≤·)
def code : Code := .seq CalibrationInput.code (WordCleanup.code clearPorts)
def changed : Finset ℕ := CalibrationInput.changed∪clearSet
def cost {n : ℕ} (a : Table n) (H B C : ℕ) : ℕ :=
  CalibrationInput.cost a H B+(clearPorts.length*(6*C+4)+1)

structure Prepared (M A L R P Q N : ℕ) (a : Table (2*aliasArraySize R)) (s : Store) : Prop where
  allocation : NatAssign.Bank ModeAllocation.ids
    (ModeAllocation.initial M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val
  rational : Ready RowArithmetic.bank ModePrelude.zeroValues s
  factor : PhysicalFactorMachine.Clean s.val
  normalization : Word s.val 351 A
  source : a.Ready s
  destination : a.OutputReady s
  floor : DyadicFloor.Clean s.val
  phase : Phase.Runtime.Clean s.val
  setup : NatAssign.Bank setupIds (initialSetup Q N) s.val
  fresh : ∀i∈TensorStart.freshPorts,Blank s.val i

private theorem blank_small {s : Store} (ready : Ready RowArithmetic.bank ModePrelude.zeroValues s)
    (i : ℕ) (hi : i∈workspace RowArithmetic.bank) (small : i<1000) : Blank s.val i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · have low : i<4 := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact ready.2 i low
  · have word := ready.1 i hi
    rw [dataValues_small _ small,RationalAccumulator.zero_word_iff_blank] at word
    exact word

private theorem ready_frame {s t : Store} (ready : Ready RowArithmetic.bank ModePrelude.zeroValues s)
    (frame : BinaryPrecision.Frame clearSet s.val t.val) (clean : ∀i∈clearSet,Blank t.val i) :
    Ready RowArithmetic.bank ModePrelude.zeroValues t := by
  refine ⟨?_,?_⟩
  · intro i hi
    by_cases hc : i∈clearSet
    · have small : i<1000 := (show ∀i∈clearSet,i∈workspace RowArithmetic.bank→i<1000 by decide)
        i hc (Finset.mem_union_right _ hi)
      rw [dataValues_small _ small,RationalAccumulator.zero_word_iff_blank]
      exact clean i hc
    · exact RationalAccumulator.word_of_eq (frame.tapes i hc) (ready.1 i hi)
  · intro i hi
    exact RationalAccumulator.blank_of_eq (frame.tapes i (by
      have := (show ∀i∈clearSet,4 ≤ i by decide)
      intro hm
      have := this i hm
      omega)) (ready.2 i hi)

theorem executes (M A L R P Q N : ℕ) (a : Table (2*aliasArraySize R))
    (canonical : TensorSetup.CanonicalHeaders a) (H B C : ℕ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ha : a.OutputReady s)
    (selected : NatAssign.Bank parameters (parameterValues M A L R P Q N) s.val)
    (headers : WordCleanup.Bounded CalibrationHandoff.targets H s.val)
    (shared : WordCleanup.Bounded ZeroInitialization.clearPorts B s.val)
    (scratch : WordCleanup.Bounded clearPorts C s.val) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost a H B C ∧
      Prepared M A L R P Q N a t ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,au,ou,ru,f0⟩ := CalibrationInput.executes a H B input tape s ha headers shared
  have bounded : WordCleanup.Bounded clearPorts C u.val := by
    intro i hi
    have hc : i∈clearSet := by simpa only [clearPorts,Finset.mem_sort] using hi
    by_cases hr : i∈workspace RowArithmetic.bank
    · have small : i<1000 := (show ∀i∈clearSet,i∈workspace RowArithmetic.bank→i<1000 by decide) i hc hr
      exact ⟨[],Nat.zero_le _,(RationalAccumulator.zero_word_iff_blank _ _).mpr (blank_small ru i hr small)⟩
    · obtain ⟨xs,hxs,word⟩ := scratch i hi
      have hh : i∉CalibrationHandoff.changed := Finset.disjoint_left.mp
        (by decide : Disjoint clearSet CalibrationHandoff.changed) hc
      exact ⟨xs,hxs,BankArray.word_of_eq (f0.tapes i (by
        simp only [CalibrationInput.changed,Finset.mem_union]
        exact not_or_intro hh hr)) word⟩
  obtain ⟨c1,t,e1,hc1,clean,frame⟩ := WordCleanup.executes clearPorts C input tape u bounded
  have seteq : clearPorts.toFinset=clearSet := by ext i;simp [clearPorts]
  rw [seteq] at frame
  have z (i : ℕ) (hi : i∈clearSet) : Blank t.val i := clean i (by simpa only [clearPorts,Finset.mem_sort] using hi)
  have rt := ready_frame ru frame z
  have keep (i : ℕ) (hi : i∈({0,1,2,3,5,6,7,8,9,37,200,202,203,204,205,210,212,213,214,215}:Finset ℕ)) :
      t.val.tapes i=u.val.tapes i := frame.tapes i
    (Finset.disjoint_left.mp (by decide : Disjoint
      ({0,1,2,3,5,6,7,8,9,37,200,202,203,204,205,210,212,213,214,215}:Finset ℕ) clearSet) hi)
  have tscratch : BankArray.Scratch t.val := by
    rcases au.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by decide)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by decide)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by decide)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩
  have seven : Blank t.val 7 := RationalAccumulator.blank_of_eq (keep 7 (by decide)) au.seven
  have ready : a.Ready t := by
    apply au.transfer frame.memory _ tscratch seven
    intro i hi
    apply keep
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
  have ot : a.OutputReady t := by
    apply ou.transfer frame.memory _ tscratch seven
    intro i hi
    apply keep
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have combined : BinaryPrecision.Frame changed s.val t.val :=
    (f0.mono Finset.subset_union_left).trans (frame.mono Finset.subset_union_right)
  have words : NatAssign.Bank parameters (parameterValues M A L R P Q N) t.val := by
    intro i hi
    exact RationalAccumulator.word_of_eq (combined.tapes i (Finset.disjoint_left.mp
      (by decide : Disjoint parameters changed) hi)) (selected i hi)
  have allocation : NatAssign.Bank ModeAllocation.ids
      (ModeAllocation.initial M L R P (addressValue a.width) (addressValue a.basePositive)
        (addressValue a.baseNegative) (addressValue a.baseDenominator)) t.val := by
    intro i hi
    by_cases hs : i∈ModeAllocation.inputs
    · simp only [ModeAllocation.inputs,Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · have word := ready.width
        rw [canonical.1] at word
        simpa [ModeAllocation.initial,RationalAccumulator.Word,BankArray.Word] using word
      · have word := ready.basePositive
        rw [canonical.2.1] at word
        simpa [ModeAllocation.initial,RationalAccumulator.Word,BankArray.Word] using word
      · have word := ready.baseNegative
        rw [canonical.2.2.1] at word
        simpa [ModeAllocation.initial,RationalAccumulator.Word,BankArray.Word] using word
      · have word := ready.baseDenominator
        rw [canonical.2.2.2] at word
        simpa [ModeAllocation.initial,RationalAccumulator.Word,BankArray.Word] using word
      · simpa [ModeAllocation.initial,parameterValues] using words 350 (by decide)
      · simpa [ModeAllocation.initial,parameterValues] using words 352 (by decide)
      · simpa [ModeAllocation.initial,parameterValues] using words 354 (by decide)
      · simpa [ModeAllocation.initial,parameterValues] using words 355 (by decide)
    · have iz : i∈clearSet := (show ModeAllocation.ids\ModeAllocation.inputs⊆clearSet by decide)
        (Finset.mem_sdiff.mpr ⟨hi,hs⟩)
      have value : ModeAllocation.initial M L R P (addressValue a.width) (addressValue a.basePositive)
          (addressValue a.baseNegative) (addressValue a.baseDenominator) i=0 := by
        simp only [ModeAllocation.inputs,Finset.mem_insert,Finset.mem_singleton] at hs
        simp only [ModeAllocation.initial]
        split_ifs <;> omega
      rw [value,RationalAccumulator.zero_word_iff_blank]
      exact z i iz
  have setup : NatAssign.Bank setupIds (initialSetup Q N) t.val := by
    intro i hi
    by_cases hQ : i=710
    · subst i;simpa [initialSetup,initialDimensions,parameterValues] using words 710 (by decide)
    by_cases hN : i=711
    · subst i;simpa [initialSetup,initialDimensions,parameterValues] using words 711 (by decide)
    have iz : i∈clearSet := (show setupIds\{710,711}⊆clearSet by decide)
      (Finset.mem_sdiff.mpr ⟨hi,by simp only [Finset.mem_insert,Finset.mem_singleton];tauto⟩)
    simpa [initialSetup,initialDimensions,hQ,hN,RationalAccumulator.zero_word_iff_blank] using z i iz
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 hc1,?_,combined⟩
  exact ⟨allocation,rt,fun i hi => z i ((show RationalRoot.ids⊆clearSet by decide) hi),
    by simpa [parameterValues] using words 351 (by decide),ready,ot,
    ⟨z 4 (by decide),fun i hi => z i ((show DyadicFloor.extraIds∪NaturalQuotient.workPorts⊆clearSet by decide) hi)⟩,
    fun i hi => z i ((show (PhaseMachine.Runtime.ids.erase 652).erase 653⊆clearSet by decide) hi),
    setup,fun i hi => z i ((show TensorStart.freshPorts⊆clearSet by decide) hi)⟩

theorem retained {s t : Store} (frame : BinaryPrecision.Frame changed s.val t.val) :
    t.val.tapes 988=s.val.tapes 988 ∧ t.val.tapes 991=s.val.tapes 991 ∧ t.val.tapes 992=s.val.tapes 992 :=
  ⟨frame.tapes 988 (by decide),frame.tapes 991 (by decide),frame.tapes 992 (by decide)⟩

#print axioms executes
#print axioms retained
end Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationStart
