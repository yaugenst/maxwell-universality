import Maxwell.Continuum.WellTargetExecution
import Maxwell.Continuum.RationalDataflowArrayIndexWrite
import Maxwell.Continuum.RationalDataflowArrayOutputCost
import Maxwell.Continuum.RationalDataflowRoundedArrayFrame

/-! Each well target is calculated, reciprocated, rounded, and written to
the actual strength table by one fixed program. The resulting memory is
the exact three-channel array update, with the reader descriptors retained. -/
namespace Maxwell.Continuum.RationalDataflow.WellTarget
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def writeCode (k : Kind) : Code := .seq (code k) (PartArray.writeAtCode 999 0)

theorem write_executes {n : ℕ} (a : PartArray.Table n) (k : Kind) (P W M : ℕ)
    (hW : 4 ≤ W) (hP : (2^P).bits.length ≤ W)
    (v : ℕ→Parts) (hw : WidthBank WellStrength.bank W v) (hg : Good WellStrength.bank v)
    (ha : (v 4).value ≠ 0) (hn : (v 1).value+target k v ≠ 0)
    (i : Fin n) (index : List Bool) (hindex : addressValue index=i.val) (hlen : index.length ≤ M)
    (hmeta : a.MetadataWidth M) (hfit : P+4096*W+4179 ≤ addressValue a.width) (hsep : a.Separated)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready WellStrength.bank v s) (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P))
    (hout : a.OutputReady s) (hi : BankArray.Word s.val 999 index) :
    ∃cost t,Executes input tape (writeCode k) cost s t ∧
      cost ≤ 2^184*(P+W+16)^2+2^20*(M+5)^2 ∧
      Ready WellStrength.bank (output k P v) t ∧ Good WellStrength.bank (output k P v) ∧
      WidthBank WellStrength.bank (P+4096*W+4179) (output k P v) ∧
      output k P v 0=Parts.literal (WellStrength.numerator P (v 1).value (target k v):ℚ) ∧
      (a.set i (output k P v 0)).OutputReady t ∧
      t.val.memory=a.writeMemory i (output k P v 0) s.val.memory ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧ BankArray.Word t.val 999 index ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧
      (∀j,300 ≤ j→j<1000→t.val.tapes j=s.val.tapes j) := by
  obtain ⟨c0,u,e0,hc0,r0,g0,w0,value0,z0,p0,f0⟩ := executes k P W hW hP v hw hg ha hn
    input tape s hr hz hp
  have out0 := hout.rounded_frame r0 f0
  have index0 : BankArray.Word u.val 999 index := BankArray.word_of_eq
    (f0.tapes 999 (DyadicFloor.StoredPower.metadata_outside WellStrength.bank 999 (by decide))) hi
  have hwidth : 0<addressValue a.width := by omega
  obtain ⟨c1,t,e1,hc1,r1,out1,memory1,f1⟩ := PartArray.writeAt_executes a WellStrength.bank 999
    (by decide) 0 (by decide) (output k P v) i hwidth ((w0 0 (by decide)).mono hfit) hsep
    input tape index hindex u r0 out0 index0
  refine ⟨c0+c1,t,e0.seq e1,?_,r1,g0,w0,value0,out1,?_,z0.write_frame f1,
    word_of_eq (f1.2.2.2.1 144 (by decide) (by decide)) p0,
    BankArray.word_of_eq (f1.2.2.2.1 999 (by decide) (by decide)) index0,
    f1.1.trans f0.inputHead,f1.2.1.trans f0.randomCursor,f1.2.2.1.trans f0.output,?_⟩
  · have hcwrite : c1 ≤ 2^20*(M+5)^2 := hc1.trans (a.writeCost_bound M hmeta index hlen _)
    omega
  · rw [memory1,f0.memory]
  · intro j hj hj'
    exact (f1.2.2.2.1 j (Or.inr (by omega)) (by omega)).trans
      (f0.tapes j (DyadicFloor.StoredPower.metadata_outside WellStrength.bank j (Or.inr ⟨by omega,hj'⟩)))

#print axioms write_executes
end Maxwell.Continuum.RationalDataflow.WellTarget
