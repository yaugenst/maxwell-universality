import Maxwell.Continuum.FourierTensorFreshComponent

/-! Three actual component runs reuse one represented normalized mode.
Only disjoint finite tape banks are fresh; mode data is preserved by the
executed row/cache memory frames. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.FreshComponent
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

def threeCode (block : ℕ) : Code := .seq (code block 0) (.seq (code (block+1) 1) (code (block+2) 2))
def threePayload (M A L R P Q N : ℕ) (a : Table (2*aliasArraySize R)) : List Bool :=
  ModeAllocation.componentPayload M A L R P Q N a 0++
    ModeAllocation.componentPayload M A L R P Q N a 1++
    ModeAllocation.componentPayload M A L R P Q N a 2

theorem Fresh.after_earlier {block later : ℕ} (before : block<later) {s t : BitRAMState}
    (h : Fresh later s) (keep : ∀i,Outside block i →t.tapes i=s.tapes i) : Fresh later t := by
  intro i lo hi
  rw [keep _ (by
    refine ⟨by unfold gap;omega,Or.inr ?_⟩
    unfold gap
    omega)]
  exact h i lo hi

theorem three_executes (M A L R P Q N E block : ℕ) [NeZero M]
    (a : Table (2*aliasArraySize R))
    (canonical : TensorSetup.CanonicalHeaders a) (valid : ∀i,(a.get i).Valid)
    (mode : ‖(GlobalPower.tableData R a).value‖≤2)
    (frequency : L*R≤2*M*Q) (mass : (6:ℝ)*RowArithmetic.rowCount R≤(2:ℝ)^E)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ha : a.OutputReady s)
    (selected : NatAssign.Bank CalibrationStart.parameters (CalibrationStart.parameterValues M A L R P Q N) s.val)
    (fresh0 : Fresh block s.val) (fresh1 : Fresh (block+1) s.val) (fresh2 : Fresh (block+2) s.val) :
    ∃steps t,Executes input tape (threeCode block) steps s t ∧ steps≤3*cost M A L R P Q N E a ∧
      t.val.output=(threePayload M A L R P Q N a).reverse++s.val.output ∧
      a.OutputReady t ∧
      NatAssign.Bank CalibrationStart.parameters (CalibrationStart.parameterValues M A L R P Q N) t.val ∧
      t.val.inputHead=s.val.inputHead ∧t.val.randomCursor=s.val.randomCursor ∧
      (∀i,4 ≤ i →(i<4+gap block ∨gap block+18000≤i) →t.val.tapes i=s.val.tapes i) ∧
      (∀limit,limit≤ModeAllocation.heapBase R a →∀k,k<limit→t.val.memory k=s.val.memory k) := by
  obtain ⟨c0,u,e0,hc0,out0,a0,params0,head0,random0,keep0,memory0⟩:=executes
    M A L R P Q N E block a 0 canonical valid mode frequency mass input tape s ha selected fresh0
  obtain ⟨c1,v,e1,hc1,out1,a1,params1,head1,random1,keep1,memory1⟩:=executes
    M A L R P Q N E (block+1) a 1 canonical valid mode frequency mass input tape u a0 params0
      (fresh1.after_earlier (by omega) keep0)
  obtain ⟨c2,t,e2,hc2,out2,a2,params2,head2,random2,keep2,memory2⟩:=executes
    M A L R P Q N E (block+2) a 2 canonical valid mode frequency mass input tape v a1 params1
      ((fresh2.after_earlier (by omega) keep0).after_earlier (by omega) keep1)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by omega,?_,a2,params2,
    head2.trans (head1.trans head0),random2.trans (random1.trans random0),?_,?_⟩
  · rw [out2,out1,out0,threePayload,List.reverse_append,List.reverse_append,List.append_assoc,
      List.append_assoc,List.append_assoc]
  · intro i lo outside
    have h0 : Outside block i := by unfold Outside;unfold gap at *;omega
    have h1 : Outside (block+1) i := by unfold Outside;unfold gap at *;omega
    have h2 : Outside (block+2) i := by unfold Outside;unfold gap at *;omega
    rw [keep2 i h2,keep1 i h1,keep0 i h0]
  · intro limit hlimit k hk
    rw [memory2 limit hlimit k hk,memory1 limit hlimit k hk,memory0 limit hlimit k hk]

#print axioms three_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.FreshComponent
