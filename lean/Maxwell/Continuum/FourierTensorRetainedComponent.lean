import Maxwell.Continuum.FourierTensorComputedWorkspace
import Maxwell.Continuum.FourierTensorCaptureFootprint
import Maxwell.Continuum.OutputCaptureDataflow
import Maxwell.Continuum.FourierTensorRetainedFootprint

/-! The actual fixed selected-template component producer supplies a
retained word. Its coefficients, physical normalization, cache, and bits
are computed by the executed program from the normalized mode table. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5500000
set_option maxRecDepth 32768

def retainedComponentCode (j : Fin 3) : Code :=
  OutputCapture.code 992 (completeComponentCode j)

theorem retainedComponent_executes {p : ℕ} (M A L R P Q N E : ℕ) [NeZero M]
    (a : Table (2*aliasArraySize R)) (old : Table p) (j : Fin 3)
    (hav : ∀i,(a.get i).Valid) (hmode : ‖(GlobalPower.tableData R a).value‖≤2)
    (hfreq : L*R≤2*M*Q) (hmass : (6:ℝ)*RowArithmetic.rowCount R≤(2:ℝ)^E)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (initial M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val)
    (hr : Ready RowArithmetic.bank ModePrelude.zeroValues s) (hz : PhysicalFactorMachine.Clean s.val)
    (wa : Word s.val 351 A)
    (ha : a.Ready s) (ho : old.OutputReady s) (hfloor : DyadicFloor.Clean s.val)
    (hphase : Phase.Runtime.Clean s.val) (hsetup : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (hfresh : ∀i∈TensorStart.freshPorts,Blank s.val i)
    (h992 : s.val.tapes 992=BitTape.blank) :
    ∃cost t,Executes input tape (retainedComponentCode j) cost s t ∧
      cost≤6*computedComponentCost M A L R P Q N E a old+7 ∧
      BankArray.Word t.val 992 (componentPayload M A L R P Q N a j) ∧
      t.val.output=s.val.output ∧
      t.val.tapes 988=s.val.tapes 988 ∧ t.val.tapes 991=s.val.tapes 991 := by
  obtain ⟨c,u,ex,hc,out⟩ := computedComponent_executes M A L R P Q N E a old j
    hav hmode hfreq hmass input tape s hb hr hz wa ha ho hfloor hphase hsetup hfresh
  obtain ⟨d,t,hd,_,et,word,output,frame⟩ := OutputCapture.executes 992 (completeComponentCode j)
    (completeComponent_avoids992 j) input tape ex _ out h992
  exact ⟨d,t,et,by omega,word,output,
    (frame.tapes 988 (by decide)).trans (completeComponent_retained ex).1,
    (frame.tapes 991 (by decide)).trans (completeComponent_retained ex).2⟩

#print axioms retainedComponent_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
