import Maxwell.Continuum.CalibrationRootProductMachine

/-! A polynomial Boolean-operation charge for the literal root summand.
The precision and all input coordinates remain runtime data. -/
namespace Maxwell.Continuum.RationalDataflow.RootProduct
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2048
attribute [local irreducible] code values

theorem costBound_polynomial (N W : ℕ) : costBound N W≤2^1500*(N+W+20)^56 := by
  generalize he : N+W+20=X
  have hX : 1≤X := by omega
  have h4 : X≤X^4 := Nat.le_self_pow (by decide) _
  have h1 : 1≤X^56 := one_le_pow₀ hX
  have h8 : X^8≤X^56 := Nat.pow_le_pow_right hX (by decide)
  have h14 : X^14≤X^56 := Nat.pow_le_pow_right hX (by decide)
  have hp : (N+6*W+20)^4≤(6*X)^4 := Nat.pow_le_pow_left (by omega) 4
  have hu : 1+N+workWidth N W+12≤2^82*X^4 := by
    have hlin : N+W+23≤2*X := by omega
    unfold workWidth coefficientWidth
    nlinarith only [hp,hlin,h4]
  have hm : 4*(workWidth N W+1)+3≤2^85*X^4 := by nlinarith only [hu]
  have hr : RootSample.costBound N W≤2^300*X^56 := by
    apply (RootSample.costBound_polynomial N W).trans
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 14).trans h14)
  have hs : Phase.Runtime.costBound 1 N (workWidth N W)≤2^1470*X^56 := by
    calc
      _≤2^322*(1+N+workWidth N W+12)^14 := Phase.Runtime.costBound_polynomial _ _ _
      _≤2^322*(2^82*X^4)^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hu 14)
      _=_ := by ring
  have ht : operationCost (4*(workWidth N W+1))≤2^270*X^56 := by
    calc
      _≤2^100*(2^85*X^4)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 2)
      _=2^270*X^8 := by ring
      _≤_ := Nat.mul_le_mul_left _ h8
  unfold costBound
  change _≤2^1500*X^56
  calc
    _≤(2^300+2*2^1470+2*2^270+1)*X^56 := by nlinarith only [hr,hs,ht,h1]
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

#print axioms costBound_polynomial

theorem compiled_run (S : Finset ℕ) (hS : inputs⊆S) (N W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) (hg : Good S v) (hN : N.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hz : Glue.Clean s.val) (hzp : Phase.Runtime.Clean s.val)
    (hp : Word s.val 640 N) (hq : Word s.val 652 1) (hn : Word s.val 653 N) :
    ∃ t,(runPriced (code.compile.next input tape) (2^1500*(N+W+20)^56+1) s.val).finished=
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (2^1500*(N+W+20)^56+1) s.val).instructions≤
        2^1500*(N+W+20)^56 ∧ Ready S (values N v) t ∧ Good S (values N v) ∧
      Glue.Clean t.val ∧ Phase.Runtime.Clean t.val ∧
      Word t.val 640 N ∧ Word t.val 652 1 ∧ Word t.val 653 N ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c,t,e,hc,hr,hg,hz,hzp,hp,hq,hn,hf⟩ := executes S hS N W v hw hg hN hW input tape s hs hz hzp hp hq hn
  have hb := hc.trans (costBound_polynomial N W)
  obtain ⟨hf',hc'⟩ := e.compiled_run (2^1500*(N+W+20)^56+1) (by omega)
  exact ⟨t,hf',hc' ▸ hb,hr,hg,hz,hzp,hp,hq,hn,hf⟩

#print axioms compiled_run
end Maxwell.Continuum.RationalDataflow.RootProduct
