import Maxwell.Continuum.RationalDataflowAntiderivativeMachine
import Maxwell.Continuum.CutoffClampMachine

/-! Fixed register operations interleaved with queries to one stored polynomial.
The query loop length remains runtime data. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff (clampControl)
set_option maxHeartbeats 2500000
set_option maxRecDepth 32768

inductive PolynomialStage where
  | arithmetic (instruction : Instruction)
  | clamp
  | query (point target : ℕ)
  deriving DecidableEq, Repr

namespace PolynomialStage

def code : PolynomialStage→Code
  | .arithmetic op => op.code
  | .clamp => clampControl.code
  | .query point target => antiderivativeCode point target

def evaluate {n : ℕ} (a : Table n) : PolynomialStage→(ℕ→Parts)→(ℕ→Parts)
  | .arithmetic op,v => op.update v
  | .clamp,v => clampControl.evaluate v
  | .query point target,v => antiderivativeState a point target v

def Valid (S : Finset ℕ) : PolynomialStage→Prop
  | .arithmetic op => op.Valid S
  | .clamp => True
  | .query point target => point∈S ∧ target∈S ∧ point≠0 ∧ point≠1 ∧ point≠2

def LiteralsFit (W : ℕ) : PolynomialStage→Prop
  | .arithmetic op => op.LiteralFits W
  | _ => True

def Admissible : PolynomialStage→(ℕ→Parts)→Prop
  | .arithmetic op,v => op.Admissible v
  | _,_ => True

def width (n W : ℕ) : ℕ := 512*(n+1)*(W+1)
def costBound (n W : ℕ) : ℕ := 2^132*(n+1)^3*(W+2)^2

theorem width_ge (n W : ℕ) : W≤width n W := by unfold width; nlinarith

theorem arithmetic_cost_le (n W : ℕ) : operationCost W≤costBound n W := by
  unfold operationCost costBound
  have hs := Nat.pow_le_pow_left (show W+3≤2*(W+2) by omega) 2
  have hp : 1≤(n+1)^3 := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul_right (2^102*(W+2)^2) hp
  nlinarith only [hs,hm,Nat.zero_le ((n+1)^3*(W+2)^2)]

theorem clamp_cost_le (n W : ℕ) :
    7*operationCost (128*(W+1))+1≤costBound n W := by
  unfold operationCost costBound
  have hs := Nat.pow_le_pow_left (show 128*(W+1)+3≤256*(W+2) by omega) 2
  have hp : 1≤(n+1)^3 := one_le_pow₀ (by omega)
  have hb : 1≤(W+2)^2 := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul_right (2^120*(W+2)^2) hp
  nlinarith only [hs,hm,hb,Nat.zero_le ((n+1)^3*(W+2)^2)]

theorem executes {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S) (op : PolynomialStage) (hop : op.Valid S)
    (W : ℕ) (hW : 2≤W) (hlit : op.LiteralsFit W)
    (hmeta : a.MetadataWidth W) (haWidth : ∀ i, (a.get i).Width W)
    (haValid : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hw : WidthBank S W v)
    (hg : Good S v) (had : op.Admissible v)
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool)
    (hlen : xs.length≤W) (hylen : ys.length≤W) (s : Store) (hn : addressValue xs=n)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ cost t finalWord, Executes input tape op.code cost s t ∧ cost≤costBound n W ∧
      RationalDataflow.Ready S (op.evaluate a v) t ∧ a.Ready t ∧
      BankArray.Word t.val 206 xs ∧ BankArray.Word t.val 201 finalWord ∧
      finalWord.length≤max xs.length ys.length ∧ Good S (op.evaluate a v) ∧
      WidthBank S (width n W) (op.evaluate a v) := by
  have outside201 : 201∉workspace S := outside_workspace S 201 (by decide)
  have outside206 : 206∉workspace S := outside_workspace S 206 (by decide)
  cases op with
  | arithmetic instruction =>
    obtain ⟨cost,t,he,hcost,hready,hframe⟩ :=
      instruction.executes S hop v W hw hlit input tape s hs
    refine ⟨cost,t,ys,he,hcost.trans (arithmetic_cost_le n W),hready,
      ha.arithmetic_frame S hframe hready.2,
      BankArray.word_of_eq (hframe.tapes 206 outside206) hsaved,
      BankArray.word_of_eq (hframe.tapes 201 outside201) hcount,
      le_max_right _ _,instruction.update_good S hop v hg had,?_⟩
    apply (instruction.update_width S hop v W hw hlit).mono
    unfold width
    nlinarith
  | clamp =>
    have valid := Calibration.RawCutoff.clampControl_valid S h0 h1 h2
    have trace := clampControl.automatic_widthTrace S valid v W hw
      (Calibration.RawCutoff.clampControl_literals W hW)
    have trace' : clampControl.WidthTrace S (128*(W+1)) v := by
      simpa only [Calibration.RawCutoff.clampControl_steps,show (2:ℕ)^7=128 by norm_num] using trace
    obtain ⟨cost,t,he,hcost,hready,hframe⟩ := clampControl.executes S valid v _ trace'
      hg (Calibration.RawCutoff.clampControl_admissible v) input tape s hs
    have hc : cost≤7*operationCost (128*(W+1))+1 := by
      simpa only [Calibration.RawCutoff.clampControl_steps] using hcost
    refine ⟨cost,t,ys,he,hc.trans (clamp_cost_le n W),hready,
      ha.arithmetic_frame S hframe hready.2,
      BankArray.word_of_eq (hframe.tapes 206 outside206) hsaved,
      BankArray.word_of_eq (hframe.tapes 201 outside201) hcount,
      le_max_right _ _,clampControl.evaluate_good S valid v hg
        (Calibration.RawCutoff.clampControl_admissible v),?_⟩
    apply trace'.result.mono
    unfold width
    nlinarith
  | query point target =>
    obtain ⟨cost,t,output,finalWord,he,hcost,hready,harray,hsaved',hcount',hlength,hgood,hwidth,
      _hvalue,_hkeep,heq⟩ := antiderivative_executes a S h0 h1 h2 point target hop.1 hop.2.1
      hop.2.2.1 hop.2.2.2.1 hop.2.2.2.2 W (by omega) hmeta haWidth haValid v hw hg
      input tape xs ys hlen s hn hsaved hcount hs ha
    subst output
    refine ⟨cost,t,finalWord,he,?_,hready,harray,hsaved',hcount',by omega,hgood,?_⟩
    · apply hcost.trans ((antiderivativeCost_polynomial n W xs.length ys.length hlen hylen).trans _)
      unfold costBound
      gcongr
      norm_num
    · apply hwidth.mono ((antiderivativeWidth_polynomial n W).trans _)
      unfold width
      nlinarith

#print axioms executes
end PolynomialStage
end Maxwell.Continuum.RationalDataflow.PartArray
