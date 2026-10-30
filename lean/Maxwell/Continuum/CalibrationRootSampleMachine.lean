import Maxwell.Continuum.CalibrationRootSample

/-! A single fixed Boolean-machine program evaluates the literal compact well
root at three runtime rational coordinates, with automatic intermediate widths. -/

namespace Maxwell.Continuum.RationalDataflow.RootSample
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 512

def argumentWidth (W : ℕ) : ℕ := 2^9*(W+1)
def costBound (N W : ℕ) : ℕ :=
  9*operationCost (argumentWidth W)+1+Glue.costBound N (argumentWidth W)

theorem glue_clean_arithmetic {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Glue.Clean s.val)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val)
    (hr : Ready S v t) : Glue.Clean t.val := by
  intro i hi
  obtain ⟨hne,hi⟩ := Finset.mem_erase.mp hi
  by_cases hs : i∈RationalDataflow.ids S
  · have hw := hr.1 i hs
    rw [dataValues_small v (Glue.ids_small i hi)] at hw
    exact (zero_word_iff_blank _ _).mp hw
  · have hg := GlueMachine.Runtime.ids_ge i hi
    have ho : i∉RationalDataflow.workspace S := by
      simp only [RationalDataflow.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      exact not_or_intro (by omega) hs
    exact blank_of_eq (f.tapes i ho) (h i (Finset.mem_erase.mpr ⟨hne,hi⟩))

theorem executes (S : Finset ℕ) (hS : inputs⊆S) (N W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) (hg : Good S v) (hN : N.bits.length≤W) (hW : 4≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hz : Glue.Clean s.val) (hp : Word s.val 640 N) :
    ∃ cost t,Executes input tape code cost s t ∧ cost≤costBound N W ∧
      Ready S (values N v) t ∧ Glue.Clean t.val ∧ Word t.val 640 N ∧
      BinaryPrecision.Frame (Glue.workspace S) s.val t.val ∧
      Good S (values N v) ∧
      (values N v 4).value=(Calibration.rootApprox (fun i => (coordinates v i).value) N).center := by
  have hvalid := argument_valid S hS
  have had := argument_admissible v
  have htrace : argument.WidthTrace S (argumentWidth W) v := by
    simpa only [argument_steps,argumentWidth] using
      argument.automatic_widthTrace S hvalid v W hw (argument_literals W (by omega))
  have hwidth := htrace.result
  have hgood := argument.evaluate_good S hvalid v hg had
  obtain ⟨c0,s0,e0,h0,b0,f0⟩ := argument.executes S hvalid v (argumentWidth W) htrace hg had input tape s hs
  have z0 := glue_clean_arithmetic hz f0 b0
  have p0 : Word s0.val 640 N := by
    apply word_of_eq (f0.tapes 640 ?_) hp
    simp only [RationalDataflow.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    exact not_or_intro (by omega) (Glue.precision_outside S)
  have hAW : W≤argumentWidth W := by unfold argumentWidth;omega
  obtain ⟨c1,t,e1,h1,b1,z1,p1,f1⟩ := Glue.executes S N 4 3
    (hS (by decide)) (hS (by decide)) (argument.evaluate v) (argumentWidth W) hwidth
    (hN.trans hAW) (hW.trans hAW) (hgood 3 (hS (by decide))) input tape s0 b0 z0 p0
  have hb : Ready S (values N v) t := by
    simpa only [values,argument_output] using b1
  have hv (i : Fin 3) : (coordinates v i).Valid := by
    apply hg i
    apply hS
    have hi := i.isLt
    simp only [inputs,Finset.mem_insert,Finset.mem_singleton]
    omega
  refine ⟨c0+c1,t,e0.seq e1,?_,hb,z1,p1,?_,?_,values_value N v hv⟩
  · simp only [argument_steps] at h0
    unfold costBound
    omega
  · apply (f0.mono ?_).trans f1
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hi)
  · exact hgood.update 4 (Glue.result_valid N _ (rawArgument_valid _ hv))

theorem costBound_polynomial (N W : ℕ) : costBound N W≤2^300*(N+W+10)^14 := by
  let X := N+W+10
  have hX : 1≤X := by dsimp [X];omega
  have h1 : 1≤X^14 := one_le_pow₀ hX
  have h2 : X^2≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have hA : argumentWidth W+3≤2^9*X := by unfold argumentWidth;dsimp [X];omega
  have hNA : N+argumentWidth W+10≤2^9*X := by unfold argumentWidth;dsimp [X];omega
  have hc : operationCost (argumentWidth W)≤2^118*X^14 := by
    calc
      _≤2^100*(2^9*X)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA 2)
      _=2^118*X^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ h2
  have hg : Glue.costBound N (argumentWidth W)≤2^296*X^14 := by
    calc
      _≤2^170*(N+argumentWidth W+10)^14 := Glue.costBound_polynomial _ _
      _≤2^170*(2^9*X)^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNA 14)
      _=_ := by ring
  unfold costBound
  change _≤2^300*X^14
  calc
    _≤(9*2^118+1+2^296)*X^14 := by nlinarith only [hc,hg,h1]
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

#print axioms executes
#print axioms costBound_polynomial
end Maxwell.Continuum.RationalDataflow.RootSample
