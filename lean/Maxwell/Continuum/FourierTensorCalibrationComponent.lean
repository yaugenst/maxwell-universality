import Maxwell.Continuum.FourierTensorCalibrationStart
import Maxwell.Continuum.FourierTensorRetainedComponent

/-! Actual component serialization from a produced calibration array.
The input still includes that array and the selected runtime parameters;
all Fourier workspace initialization is performed by the fixed program. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationStart
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
set_option maxHeartbeats 5500000
set_option maxRecDepth 65536

def componentCode (j : Fin 3) : Code := .seq code (ModeAllocation.completeComponentCode j)
def componentCost (M A L R P Q N E H B C : ℕ) (a : Table (2*aliasArraySize R)) : ℕ :=
  cost a H B C+ModeAllocation.computedComponentCost M A L R P Q N E a a
def retainedCode (j : Fin 3) : Code := .seq code (ModeAllocation.retainedComponentCode j)

private theorem cleanup_protects (port : ℕ) (ports : List ℕ) (outside : port∉ports) :
    (WordCleanup.code ports).protectsTape port=true := by
  induction ports with
  | nil => rfl
  | cons i rest ih =>
    have hi : port≠i := fun h => outside (by simp [h])
    have hr : port∉rest := fun h => outside (List.mem_cons_of_mem _ h)
    change (BitRAM.protectsTape (TapeOps.clear i) port && (WordCleanup.code rest).protectsTape port)=true
    rw [Bool.and_eq_true]
    exact ⟨by simp [BitRAM.protectsTape,TapeOps.clear,BitRAMInstruction.protectsTape,hi,ne_comm],ih hr⟩

private theorem code_protects (port : ℕ) (hp : port=988 ∨ port=991 ∨ port=992) :
    code.protectsTape port=true := by
  have first := cleanup_protects port ZeroInitialization.clearPorts (by
    simp only [ZeroInitialization.clearPorts,Finset.mem_sort]
    rcases hp with rfl|rfl|rfl <;> decide)
  have last := cleanup_protects port clearPorts (by
    simp only [clearPorts,Finset.mem_sort]
    rcases hp with rfl|rfl|rfl <;> decide)
  have handoff : CalibrationHandoff.code.protectsTape port=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  have plan : (NatAssign.code ZeroInitialization.plan).protectsTape port=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  change ((CalibrationHandoff.code.protectsTape port &&
    ((WordCleanup.code ZeroInitialization.clearPorts).protectsTape port &&
      (NatAssign.code ZeroInitialization.plan).protectsTape port)) &&
        (WordCleanup.code clearPorts).protectsTape port)=true
  simp only [Bool.and_eq_true]
  exact ⟨⟨handoff,first,plan⟩,last⟩

theorem component_executes (M A L R P Q N E : ℕ) [NeZero M]
    (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (canonical : TensorSetup.CanonicalHeaders a) (valid : ∀i,(a.get i).Valid)
    (mode : ‖(GlobalPower.tableData R a).value‖≤2)
    (frequency : L*R≤2*M*Q) (mass : (6:ℝ)*RowArithmetic.rowCount R≤(2:ℝ)^E)
    (H B C : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store) (ha : a.OutputReady s)
    (selected : NatAssign.Bank parameters (parameterValues M A L R P Q N) s.val)
    (headers : WordCleanup.Bounded CalibrationHandoff.targets H s.val)
    (shared : WordCleanup.Bounded ZeroInitialization.clearPorts B s.val)
    (scratch : WordCleanup.Bounded clearPorts C s.val) :
    ∃steps t,Executes input tape (componentCode j) steps s t ∧
      steps≤componentCost M A L R P Q N E H B C a ∧
      t.val.output=(ModeAllocation.componentPayload M A L R P Q N a j).reverse++s.val.output ∧
      NatAssign.Scratch t.val ∧
      (∀limit,limit≤ModeAllocation.heapBase R a →∀k,k<limit→t.val.memory k=s.val.memory k) := by
  obtain ⟨c0,u,e0,hc0,ready,frame⟩ := executes M A L R P Q N a canonical H B C
    input tape s ha selected headers shared scratch
  obtain ⟨c1,t,e1,hc1,output,clean,memory⟩ := ModeAllocation.computedComponent_executes M A L R P Q N E a a j
    valid mode frequency mass input tape u ready.allocation ready.rational ready.factor
    ready.normalization ready.source ready.destination ready.floor ready.phase ready.setup ready.fresh
  exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 hc1,by simpa only [frame.output] using output,clean,
    fun limit hlimit k hk=>by rw [memory limit hlimit k hk,frame.memory]⟩

theorem component_retained {input : List Bool} {tape : ℕ→Bool} {j : Fin 3}
    {steps : ℕ} {s t : Store} (run : Executes input tape (componentCode j) steps s t) :
    t.val.tapes 988=s.val.tapes 988 ∧ t.val.tapes 991=s.val.tapes 991 ∧ t.val.tapes 992=s.val.tapes 992 := by
  have protect : (componentCode j).protectsTape 988=true ∧
      (componentCode j).protectsTape 991=true ∧ (componentCode j).protectsTape 992=true := by
    change (code.protectsTape 988 && (ModeAllocation.completeComponentCode j).protectsTape 988)=true ∧
      (code.protectsTape 991 && (ModeAllocation.completeComponentCode j).protectsTape 991)=true ∧
      (code.protectsTape 992 && (ModeAllocation.completeComponentCode j).protectsTape 992)=true
    simp only [Bool.and_eq_true]
    exact ⟨⟨code_protects 988 (by tauto),ModeAllocation.completeComponent_protects988 j⟩,
      ⟨code_protects 991 (by tauto),ModeAllocation.completeComponent_protects991 j⟩,
      ⟨code_protects 992 (by tauto),OutputCapture.avoidsCode_protectsTape _ _ (ModeAllocation.completeComponent_avoids992 j)⟩⟩
  exact ⟨run.protectsTape 988 protect.1,run.protectsTape 991 protect.2.1,run.protectsTape 992 protect.2.2⟩

theorem retained_executes (M A L R P Q N E : ℕ) [NeZero M]
    (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (canonical : TensorSetup.CanonicalHeaders a) (valid : ∀i,(a.get i).Valid)
    (mode : ‖(GlobalPower.tableData R a).value‖≤2)
    (frequency : L*R≤2*M*Q) (mass : (6:ℝ)*RowArithmetic.rowCount R≤(2:ℝ)^E)
    (H B C : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store) (ha : a.OutputReady s)
    (selected : NatAssign.Bank parameters (parameterValues M A L R P Q N) s.val)
    (headers : WordCleanup.Bounded CalibrationHandoff.targets H s.val)
    (shared : WordCleanup.Bounded ZeroInitialization.clearPorts B s.val)
    (scratch : WordCleanup.Bounded clearPorts C s.val) (archive : s.val.tapes 992=BitTape.blank) :
    ∃steps t,Executes input tape (retainedCode j) steps s t ∧
      steps≤cost a H B C+6*ModeAllocation.computedComponentCost M A L R P Q N E a a+7 ∧
      BankArray.Word t.val 992 (ModeAllocation.componentPayload M A L R P Q N a j) ∧
      t.val.output=s.val.output ∧ t.val.tapes 988=s.val.tapes 988 ∧ t.val.tapes 991=s.val.tapes 991 := by
  obtain ⟨c0,u,e0,hc0,ready,frame⟩ := executes M A L R P Q N a canonical H B C
    input tape s ha selected headers shared scratch
  have previous := retained frame
  obtain ⟨c1,t,e1,hc1,word,output,count,profile⟩ := ModeAllocation.retainedComponent_executes
    M A L R P Q N E a a j valid mode frequency mass input tape u
    ready.allocation ready.rational ready.factor ready.normalization ready.source ready.destination
    ready.floor ready.phase ready.setup ready.fresh (previous.2.2.trans archive)
  exact ⟨c0+c1,t,e0.seq e1,by omega,word,output.trans frame.output,
    count.trans previous.1,profile.trans previous.2.1⟩

#print axioms component_executes
#print axioms component_retained
#print axioms retained_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationStart
