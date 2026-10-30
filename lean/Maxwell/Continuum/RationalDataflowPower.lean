import Maxwell.Continuum.RationalDataflowCounted
import Maxwell.Continuum.RationalDataflowTrace
import Maxwell.Continuum.CutoffRawArithmetic

/-! One fixed program computes rational powers from a runtime exponent word. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff (power power_valid power_width power_value)
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def powerBody (target source : ℕ) : Control :=
  .step (.binary .mul target target source) .done

def powerProgram (countTape target source : ℕ) : Code :=
  .seq (NatAssign.code (literalStage target (Parts.literal 1)))
    (countedProgram countTape (powerBody target source).code)

def powerWidth (n W : ℕ) : ℕ := (n+1)*(W+1)+1

theorem powerBody_iterate (target source : ℕ) (hne : source≠target) (v : ℕ→Parts) (n : ℕ) :
    iterateControl (powerBody target source) (Function.update v target (Parts.literal 1)) n=
      Function.update v target (power (v source) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterateControl,ih]
    simp only [powerBody,Control.evaluate,Instruction.update,BinaryOp.eval,Function.update_self,
      Function.update_of_ne hne,Function.update_idem,power]

theorem power_bank_width (S : Finset ℕ) (target : ℕ) (v : ℕ→Parts) (source n W k : ℕ)
    (hs : source∈S) (hw : WidthBank S W v) (hk : k≤n) :
    WidthBank S (powerWidth n W) (Function.update v target (power (v source) k)) := by
  apply WidthBank.update (hw.mono (by unfold powerWidth; nlinarith))
  apply (power_width (hw source hs) k).mono
  unfold powerWidth
  have hh := Nat.mul_le_mul_right (W+1) hk
  nlinarith only [hh]

theorem powerBody_widthTrace (S : Finset ℕ) (target source n W : ℕ)
    (hne : source≠target) (hs : source∈S) (v : ℕ→Parts) (hw : WidthBank S W v)
    (k : ℕ) (hk : k<n) :
    (powerBody target source).WidthTrace S (powerWidth n W)
      (iterateControl (powerBody target source) (Function.update v target (Parts.literal 1)) k) := by
  rw [powerBody_iterate target source hne v k]
  refine ⟨power_bank_width S target v source n W k hs hw hk.le,trivial,?_⟩
  change WidthBank S (powerWidth n W)
    (Function.update (Function.update v target (power (v source) k)) target
      ((Function.update v target (power (v source) k) target).mul
        (Function.update v target (power (v source) k) source)))
  simp only [Function.update_self,Function.update_of_ne hne,Function.update_idem]
  exact power_bank_width S target v source n W (k+1) hs hw hk

def powerCost (n W wordLength : ℕ) : ℕ := stageCost (powerWidth n W)+
  (n+1)*(13*wordLength+15)+n*(operationCost (powerWidth n W)+1)

theorem power_executes (S : Finset ℕ) (countTape target source : ℕ)
    (hc : countTape∉workspace S) (ht : target∈S) (hs' : source∈S) (hne : source≠target)
    (v : ℕ→Parts) (n W : ℕ) (hw : WidthBank S W v) (hg : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue xs=n) (hcount : s.val.tapes countTape=BitTape.shifted xs origin)
    (hs : Ready S v s) :
    ∃ cost t, Executes input tape (powerProgram countTape target source) cost s t ∧
      cost≤powerCost n W xs.length ∧ Ready S (Function.update v target (power (v source) n)) t := by
  have hWB : W≤powerWidth n W := by unfold powerWidth; nlinarith
  have h1 : (Parts.literal (1:ℚ)).Width (powerWidth n W) :=
    (Parts.literal_width RationalWords.width_one).mono (by unfold powerWidth; omega)
  obtain ⟨c0,s0,e0,h0,b0,f0⟩ := literal_executes S target ht (Parts.literal 1) v (powerWidth n W)
    h1 (hw.mono hWB) input tape s hs
  have hvalid : (powerBody target source).Valid S := ⟨⟨ht,ht,hs'⟩,trivial⟩
  have hgood (k : ℕ) (_hk : k<n) :
      Good S (iterateControl (powerBody target source) (Function.update v target (Parts.literal 1)) k) := by
    rw [powerBody_iterate target source hne v k]
    exact hg.update target (power_valid _ (hg source hs') k)
  have had (k : ℕ) (_hk : k<n) :
      (powerBody target source).AdmissibleTrace
        (iterateControl (powerBody target source) (Function.update v target (Parts.literal 1)) k) :=
    ⟨trivial,trivial⟩
  obtain ⟨c1,t,_,e1,hb,_,_,hbound⟩ := controlCounted_executes S countTape hc
    (powerBody target source) hvalid n (powerWidth n W) (Function.update v target (Parts.literal 1))
    (powerBody_widthTrace S target source n W hne hs' v hw) hgood had input tape xs origin s0 hn
    ((f0.tapes countTape hc).trans hcount) b0
  rw [powerBody_iterate target source hne v n] at hb
  refine ⟨c0+c1,t,e0.seq e1,?_,hb⟩
  simp only [powerBody,Control.steps,Nat.add_zero,Nat.one_mul] at hbound
  unfold powerCost
  omega

theorem power_computes (S : Finset ℕ) (countTape target source : ℕ)
    (hc : countTape∉workspace S) (ht : target∈S) (hs' : source∈S) (hne : source≠target)
    (v : ℕ→Parts) (n W : ℕ) (hw : WidthBank S W v) (hg : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue xs=n) (hcount : s.val.tapes countTape=BitTape.shifted xs origin)
    (hs : Ready S v s) :
    ∃ cost t output,
      (runPriced ((powerProgram countTape target source).compile.next input tape)
        (powerCost n W xs.length+1) s.val).finished=some (t.place (powerProgram countTape target source).size) ∧
      cost≤powerCost n W xs.length ∧ Ready S output t ∧ (output target).value=(v source).value^n := by
  obtain ⟨cost,t,he,hc',hb⟩ := power_executes S countTape target source hc ht hs' hne v n W hw hg
    input tape xs origin s hn hcount hs
  obtain ⟨hrun,_⟩ := he.compiled_run (powerCost n W xs.length+1) (by omega)
  refine ⟨cost,t,Function.update v target (power (v source) n),hrun,hc',hb,?_⟩
  simpa only [Function.update_self] using power_value (v source) n

#print axioms power_computes

end Maxwell.Continuum.RationalDataflow
