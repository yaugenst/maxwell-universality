import Maxwell.Continuum.WellAxisArithmetic
import Maxwell.Continuum.WellTargetWrite

/-! The mediator step selects its coupling by executed coordinate tests,
then computes and stores the rounded reciprocal strength. -/
namespace Maxwell.Continuum.RationalDataflow.WellMediatorWrite
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def code : Code := .seq WellAxisMachine.control.code (WellTarget.writeCode .mediator)

def target (v : ℕ→Parts) : ℚ := -(WellAxisMachine.selected v)^2/(v 4).value

def output (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  WellTarget.output .mediator P (WellAxisMachine.control.evaluate v)

theorem selected_target (v : ℕ→Parts) (hg : Good WellStrength.bank v) :
    WellTarget.target .mediator (WellAxisMachine.control.evaluate v)=target v := by
  simp only [WellTarget.target,target,WellAxisMachine.output_value v hg,
    WellAxisMachine.preserves v 4 (by decide) (by decide) (by decide)]

theorem executes {n : ℕ} (a : PartArray.Table n) (P W M : ℕ)
    (hW : 4 ≤ W) (hP : (2^P).bits.length ≤ W)
    (v : ℕ→Parts) (hw : WidthBank WellStrength.bank W v) (hg : Good WellStrength.bank v)
    (ha : (v 4).value ≠ 0) (hn : (v 1).value+target v ≠ 0)
    (i : Fin n) (index : List Bool) (hindex : addressValue index=i.val) (hlen : index.length ≤ M)
    (hmeta : a.MetadataWidth M) (hfit : P+4096*(256*(W+1))+4179 ≤ addressValue a.width) (hsep : a.Separated)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready WellStrength.bank v s) (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P))
    (hout : a.OutputReady s) (hi : BankArray.Word s.val 999 index) :
    ∃cost t,Executes input tape code cost s t ∧
      cost ≤ 2^126*(W+2)^2+2^184*(P+256*(W+1)+16)^2+2^20*(M+5)^2 ∧
      Ready WellStrength.bank (output P v) t ∧ Good WellStrength.bank (output P v) ∧
      WidthBank WellStrength.bank (P+4096*(256*(W+1))+4179) (output P v) ∧
      output P v 0=Parts.literal (WellStrength.numerator P (v 1).value (target v):ℚ) ∧
      (a.set i (output P v 0)).OutputReady t ∧
      t.val.memory=a.writeMemory i (output P v 0) s.val.memory ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧ BankArray.Word t.val 999 index ∧
      (∀j,300 ≤ j→j<1000→t.val.tapes j=s.val.tapes j) := by
  obtain ⟨c0,u,e0,hc0,r0,g0,w0,_,f0⟩ := WellAxisMachine.executes v W (by omega) hw hg
    input tape s hr
  have mid0 := WellAxisMachine.preserves v 1 (by decide) (by decide) (by decide)
  have scale0 := WellAxisMachine.preserves v 4 (by decide) (by decide) (by decide)
  have target0 := selected_target v hg
  have out0 := hout.rounded_frame r0
    (f0.mono (RoundedInteger.arithmetic_workspace_subset WellStrength.bank))
  have power0 : Word u.val 144 (2^P) := word_of_eq
    (f0.tapes 144 (outside_workspace WellStrength.bank 144 (by decide))) hp
  have index0 : BankArray.Word u.val 999 index := BankArray.word_of_eq
    (f0.tapes 999 (outside_workspace WellStrength.bank 999 (by decide))) hi
  obtain ⟨c1,t,e1,hc1,r1,g1,w1,value1,out1,memory1,z1,p1,index1,_,_,_,f1⟩ :=
    WellTarget.write_executes a .mediator P (256*(W+1)) M (by omega) (hP.trans (by omega))
      _ w0 g0 (by rwa [scale0]) (by rwa [mid0,target0]) i index hindex hlen hmeta hfit hsep
      input tape u r0 (hz.arithmetic_frame f0) power0 out0 index0
  rw [mid0,target0] at value1
  refine ⟨c0+c1,t,e0.seq e1,by omega,r1,g1,w1,value1,out1,?_,z1,p1,index1,?_⟩
  · rw [memory1,f0.memory]
    rfl
  · intro j hj hj'
    exact (f1 j hj hj').trans
      (f0.tapes j (outside_workspace WellStrength.bank j (Or.inr ⟨by omega,hj'⟩)))

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellMediatorWrite
