import Maxwell.Continuum.FourierTensorFreshComponentInput
import Maxwell.Cost.ArrayPrefixFrame

/-! One actual Fourier component runs in a disjoint fresh tape bank. The
original normalized mode and its parameter words survive, so the next
component can reuse them without a caller-supplied rerun state. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.FreshComponent
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

def code (block : ℕ) (j : Fin 3) : Code := .seq (copyCode block)
  (.call ((CalibrationStart.componentCode j).compile.renameTapes (relocation block)))
def cost (M A L R P Q N E : ℕ) (a : Table (2*aliasArraySize R)) : ℕ :=
  copyCost a (CalibrationStart.parameterValues M A L R P Q N)+
    CalibrationStart.componentCost M A L R P Q N E 0 0 0 a+1

def Outside (block i : ℕ) : Prop := 4 ≤ i ∧ (i<4+gap block ∨gap block+6000≤i)

theorem outside_source (block i : ℕ) (lo : 4 ≤ i) (hi : i<6000) : Outside block i := by
  refine ⟨lo,Or.inl ?_⟩
  unfold gap
  omega

theorem executes (M A L R P Q N E block : ℕ) [NeZero M]
    (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (canonical : TensorSetup.CanonicalHeaders a) (valid : ∀i,(a.get i).Valid)
    (mode : ‖(GlobalPower.tableData R a).value‖≤2)
    (frequency : L*R≤2*M*Q) (mass : (6:ℝ)*RowArithmetic.rowCount R≤(2:ℝ)^E)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ha : a.OutputReady s)
    (selected : NatAssign.Bank CalibrationStart.parameters (CalibrationStart.parameterValues M A L R P Q N) s.val)
    (fresh : Fresh block s.val) :
    ∃steps t,Executes input tape (code block j) steps s t ∧ steps≤cost M A L R P Q N E a ∧
      t.val.output=(ModeAllocation.componentPayload M A L R P Q N a j).reverse++s.val.output ∧
      a.OutputReady t ∧
      NatAssign.Bank CalibrationStart.parameters (CalibrationStart.parameterValues M A L R P Q N) t.val ∧
      t.val.inputHead=s.val.inputHead ∧t.val.randomCursor=s.val.randomCursor ∧
      (∀i,Outside block i →t.val.tapes i=s.val.tapes i) ∧
      (∀limit,limit≤ModeAllocation.heapBase R a →∀k,k<limit→t.val.memory k=s.val.memory k) := by
  obtain ⟨c0,u,e0,hc0,prepared,frame⟩:=copy_executes M A L R P Q N block a input tape s ha selected fresh
  obtain ⟨c1,v,e1,hc1,output,clean,memory⟩:=CalibrationStart.component_executes M A L R P Q N E a j
    canonical valid mode frequency mass 0 0 0 input tape (u.renameTapes (relocation block))
    prepared.table prepared.selected prepared.headers prepared.shared prepared.scratch
  have run:=e1.renamed_call (relocation block)
  rw [Store.renameTapes_symm (relocation block) u] at run
  let t:=v.renameTapes (relocation block)
  have keep (i : ℕ) (hi : Outside block i) : t.val.tapes i=s.val.tapes i := by
    have separated : 6000≤gap block := by unfold gap;omega
    have upper : 6000≤relocation block i := by
      change 6000≤TapeBlockSwap.index 4 5996 (gap block) i
      unfold TapeBlockSwap.index
      split_ifs <;> rcases hi with ⟨lo,hi⟩ <;> omega
    change v.val.tapes (relocation block i)=_
    rw [e1.tapesBelow (CalibrationStart.component_below j) _ upper]
    change u.val.tapes (relocation block (relocation block i))=_
    rw [TapeBlockSwap.involutive 4 5996 (gap block) _ i]
    apply frame.tapes
    rw [targets_eq]
    intro member
    obtain ⟨k,hk,equal⟩:=Finset.mem_image.mp member
    have range:=sources_range k hk
    rcases hi with ⟨_,hi⟩
    omega
  have cleanT : NatAssign.Scratch t.val := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (show t.val.tapes i=v.val.tapes i from ?_) (clean i hi)
    change v.val.tapes (relocation block i)=_
    rw [relocation_small block i hi]
  have keepSmall (i : ℕ) (lo : 4 ≤ i) (hi : i<6000) := keep i (outside_source block i lo hi)
  have memoryT (limit : ℕ) (hlimit : limit≤ModeAllocation.heapBase R a) (k : ℕ) (hk : k<limit) :
      t.val.memory k=s.val.memory k := by
    change v.val.memory k=_
    rw [memory limit hlimit k hk]
    change u.val.memory k=_
    rw [frame.memory]
  have scratchT : BankArray.Scratch t.val :=
    ⟨cleanT 0 (by decide),cleanT 1 (by decide),cleanT 2 (by decide),cleanT 3 (by decide),
      RationalAccumulator.blank_of_eq (keepSmall 5 (by decide) (by decide)) ha.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keepSmall 6 (by decide) (by decide)) ha.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keepSmall 8 (by decide) (by decide)) ha.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keepSmall 9 (by decide) (by decide)) ha.scratch.2.2.2.2.2.2.2⟩
  have table : a.OutputReady t := by
    refine ⟨scratchT,RationalAccumulator.blank_of_eq (keepSmall 7 (by decide) (by decide)) ha.seven,
      RationalAccumulator.blank_of_eq (keepSmall 37 (by decide) (by decide)) ha.packing,
      BankArray.word_of_eq (keepSmall 210 (by decide) (by decide)) ha.width,
      BankArray.word_of_eq (keepSmall 212 (by decide) (by decide)) ha.basePositive,
      BankArray.word_of_eq (keepSmall 213 (by decide) (by decide)) ha.baseNegative,
      BankArray.word_of_eq (keepSmall 214 (by decide) (by decide)) ha.baseDenominator,
      BankArray.word_of_eq (keepSmall 215 (by decide) (by decide)) ha.clock,?_,?_,?_⟩
    · exact ha.positive.memoryPrefix (by unfold ModeAllocation.heapBase ModeAllocation.heap;omega)
        (memoryT (ModeAllocation.heapBase R a) le_rfl)
    · exact ha.negative.memoryPrefix (by unfold ModeAllocation.heapBase ModeAllocation.heap;omega)
        (memoryT (ModeAllocation.heapBase R a) le_rfl)
    · exact ha.denominator.memoryPrefix (by unfold ModeAllocation.heapBase ModeAllocation.heap;omega)
        (memoryT (ModeAllocation.heapBase R a) le_rfl)
  have positions:=e1.protectsInputPositions (CalibrationStart.component_positions j)
  refine ⟨c0+(c1+1),t,e0.seq run,by unfold cost;omega,?_,table,?_,
    positions.1.trans frame.inputHead,positions.2.trans frame.randomCursor,keep,memoryT⟩
  · change v.val.output=_
    rw [output]
    change _++u.val.output=_
    rw [frame.output]
  · intro i hi
    have range:=sources_range i ((by decide : CalibrationStart.parameters⊆ports) hi)
    exact RationalAccumulator.word_of_eq (keepSmall i range.1 range.2) (selected i hi)

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.FreshComponent
