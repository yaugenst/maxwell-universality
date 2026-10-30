import Maxwell.Continuum.PhaseDataflowExecution
import Maxwell.Continuum.PhaseMachineFinalCost

/-! Uniform bit-operation and raw-word bounds for repeated phase calls. -/
namespace Maxwell.Continuum.RationalDataflow.Phase
open Maxwell.Cost Maxwell.Cost.Structured RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem workWidth_polynomial (Q N W : ℕ) :
    workWidth Q N W+2≤2^68*(Q+N+W+12)^4 := by
  have hf := PhaseMachine.fullFinalWidth_polynomial Q N (W+1)
  have hs : PhaseMachine.sizeParameter Q N (W+1)≤Q+N+W+12 := by
    unfold PhaseMachine.sizeParameter
    omega
  have hh := hf.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 4))
  have hW : W+3≤(Q+N+W+12)^4 :=
    (by omega : W+3≤Q+N+W+12).trans (Nat.le_self_pow (by decide) _)
  unfold workWidth
  nlinarith only [hh,hW]

theorem costBound_polynomial (Q N W : ℕ) : costBound Q N W≤2^300*(Q+N+W+12)^14 := by
  let X := Q+N+W+12
  have hX : 1≤X := by dsimp [X];omega
  have hW : W+3≤X := by dsimp [X];omega
  have h2 : X^2≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have h8 : X^8≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have h1 : 1≤X^14 := one_le_pow₀ hX
  have hlinear : X≤X^14 := Nat.le_self_pow (by decide) _
  have hw := workWidth_polynomial Q N W
  have hc : sharedStageCost (workWidth Q N W)≤2^296*X^14 := by
    unfold sharedStageCost
    calc
      _ ≤ 2^160*(2^68*X^4)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2)
      _ = 2^296*X^8 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h8
  have hp : sharedStageCost W≤2^160*X^14 := by
    unfold sharedStageCost
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega : W+2≤X) 2).trans h2)
  have hp' : sharedStageCost (W+1)≤2^160*X^14 := by
    unfold sharedStageCost
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega : W+1+2≤X) 2).trans h2)
  have hf : PhaseMachine.fullCost Q N (W+1)+1≤2^220*X^14 :=
    (PhaseMachine.fullCost_polynomial _ _ _).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by unfold PhaseMachine.sizeParameter;dsimp [X];omega) 14))
  unfold costBound
  change _≤2^300*X^14
  have hg : 300*(2*W+4)+2≤602*X^14 := by omega
  calc
    _ ≤ (2^160+602+2^160+2^220+2^296)*X^14 := by omega
    _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

theorem result_width (base : ℕ→Sign) (Q N W : ℕ) (x : Parts) (hx : x.Width W) :
    (result base Q N x).Width (2^68*(Q+N+W+12)^4) := by
  have hm : (magnitude x).bits.length≤W+1 :=
    (IntegerNormSquare.magnitude_bits_length_le _ _).trans
      (Nat.add_le_add_right (max_le hx.1 hx.2.1) 1)
  have hd := hx.2.2.trans (Nat.le_succ W)
  have hf (i : ℕ) (hi : i∈PhaseMachine.allIds) :=
    PhaseMachine.fullFinal_width (negative x) base (magnitude x) x.denominator Q N (W+1) hm hd i hi
  have hw : PhaseMachine.fullFinalWidth Q N (W+1)≤2^68*(Q+N+W+12)^4 :=
    (by unfold workWidth;omega : PhaseMachine.fullFinalWidth Q N (W+1)≤workWidth Q N W+2).trans
      (workWidth_polynomial Q N W)
  exact ⟨(hf 602 (by decide)).trans hw,(hf 603 (by decide)).trans hw,(hf 604 (by decide)).trans hw⟩

theorem compiled_run (S : Finset ℕ) (base : ℕ→Sign) (Q N target source : ℕ)
    (ht : target∈S) (hs' : source∈S) (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : RationalDataflow.Ready S v s)
    (hz : Clean s.val) :
    ∃ t, (runPriced ((code base Q N target source).compile.next input tape)
      (2^300*(Q+N+W+12)^14+1) s.val).finished=some (t.place (code base Q N target source).size) ∧
      (runPriced ((code base Q N target source).compile.next input tape)
      (2^300*(Q+N+W+12)^14+1) s.val).instructions≤2^300*(Q+N+W+12)^14 ∧
      RationalDataflow.Ready S (Function.update v target (result base Q N (v source))) t ∧
      Clean t.val ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,he,hc,hr,hz',hf⟩ := executes S base Q N target source ht hs' v W hw input tape s hs hz
  have hcost := hc.trans (costBound_polynomial Q N W)
  have hout := he.compiled_run (2^300*(Q+N+W+12)^14+1) (by omega)
  exact ⟨t,hout.1,hout.2 ▸ hcost,hr,hz',hf⟩

#print axioms costBound_polynomial
#print axioms compiled_run
end Maxwell.Continuum.RationalDataflow.Phase
