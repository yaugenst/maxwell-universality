import Maxwell.Continuum.StoredSourceRead
import Maxwell.Continuum.RoundedIntegerRegister
import Maxwell.Continuum.RationalDataflowFixedWidths

/-! Actual multiplication and floor-dyadic rounding of each parsed source
entry. The common calibrated multiplier remains in raw register 13. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def bank : Finset ℕ := {0,1,4,12,13,14,15}
def multiply : RationalDataflow.Instruction := .binary .mul 12 0 13
def amplitudeCode : Code := .seq multiply.code (RoundedInteger.code 0 12)
def amplitudeValues (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (multiply.update v) 0 (RoundedInteger.result P (multiply.update v 12))
def numerator (P : ℕ) (v : ℕ→Parts) : ℤ :=
  (roundDyadic P ((v 0).value*(v 13).value)).numerator

theorem amplitude_result (P : ℕ) (v : ℕ→Parts) :
    amplitudeValues P v 0=Parts.literal (numerator P v:ℚ) := by
  simp only [amplitudeValues,Function.update_self,RoundedInteger.result,
    multiply,Instruction.update,BinaryOp.eval,Parts.mul_value,numerator]

theorem amplitude_kept (P : ℕ) (v : ℕ→Parts) (i : ℕ)
    (h0 : i≠0) (h12 : i≠12) (_h14 : i≠14) (_h15 : i≠15) :
    amplitudeValues P v i=v i := by
  simp only [amplitudeValues,Instruction.update,multiply,
    Function.update_of_ne h0,Function.update_of_ne h12]

theorem amplitude_executes (P B : ℕ) (_hB : 2≤B)
    (_hP : (2^P).bits.length≤B) (v : ℕ→Parts)
    (width : WidthBank bank B v) (good : Good bank v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready bank v s)
    (clean : DyadicFloor.Clean s.val) (power : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape amplitudeCode cost s t ∧
      cost≤2^165*(P+B+8)^2 ∧ Ready bank (amplitudeValues P v) t ∧
      Good bank (amplitudeValues P v) ∧ WidthBank bank (P+32*B+35) (amplitudeValues P v) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace bank) s.val t.val := by
  have valid : multiply.Valid bank:=by simp [multiply,Instruction.Valid,bank]
  obtain ⟨c0,a,e0,hc0,ra,f0⟩:=multiply.executes bank valid v B width trivial input tape s ready
  have wa:=multiply.update_width bank valid v B width trivial
  have ga:=multiply.update_good bank valid v good trivial
  have pa : Word a.val 144 (2^P):=word_of_eq
    (f0.tapes 144 (outside_workspace bank 144 (by decide))) power
  obtain ⟨c1,t,e1,hc1,rt,wt,ct,pt,f1⟩:=RoundedInteger.executes bank P 0 12
    (by decide) (by decide) (multiply.update v) (2*B+1) wa (ga 12 (by decide))
    input tape a ra (clean.arithmetic_frame f0) pa
  refine ⟨c0+c1,t,e0.seq e1,?_,rt,ga.update 0 (RoundedInteger.result_valid _ _),
    wt.mono (by omega),ct,pt,
    (f0.mono (RoundedInteger.arithmetic_workspace_subset bank)).trans f1⟩
  unfold operationCost at hc0
  nlinarith only [hc0,hc1,Nat.zero_le P,Nat.zero_le B]

#print axioms amplitude_executes
end Maxwell.Continuum.SourcePayload
