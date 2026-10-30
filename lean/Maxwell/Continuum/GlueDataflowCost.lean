import Maxwell.Continuum.GlueDataflowExecution

/-! Polynomial charged execution of the fixed signed glue evaluator, with
literal approximation semantics and reusable private-storage cleanup. -/
namespace Maxwell.Continuum.RationalDataflow.Glue
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem costBound_polynomial (N W : ℕ) : costBound N W≤2^170*(N+W+10)^14 := by
  let X := N+W+10
  have hX : 1≤X := by dsimp [X];omega
  have h1 : 1≤X^14 := one_le_pow₀ hX
  have hx : X≤X^14 := Nat.le_self_pow (by decide) _
  have hx2 : X^2≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have hx8 : X^8≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have hs (B : ℕ) (hb : B+2≤X) : stageCost B≤2^96*X^14 := by
    unfold stageCost
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hb 2).trans hx2)
  have hs0 := hs W (by dsimp [X];omega)
  have hs1 := hs (W+1) (by dsimp [X];omega)
  have hm : 300*(2*W+4)≤2^10*X^14 := by
    have hsmall : 2*W+4≤2*X := by dsimp [X];omega
    nlinarith only [hsmall,hx]
  have he : GlueMachine.Runtime.costBound N (W+1)≤2^124*X^14 := by
    apply (GlueMachine.Runtime.costBound_polynomial N (W+1)).trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [X];omega) 14)
  have hk : 6*(GlueMachine.order N).bits.length+4≤2^10*X^14 := by
    have hb := RationalTaylor.nat_bits_le_self (GlueMachine.order N)
    have ho : GlueMachine.order N+2≤16*X^2 :=
      (GlueMachine.Runtime.order_bound N W).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [X];omega) 2))
    nlinarith only [hb,ho,hx2,h1]
  have hw : workWidth N W+2≤2^33*X^4 := by
    have hp : (N+W+9)^4≤X^4 := Nat.pow_le_pow_left (by dsimp [X];omega) 4
    have hpow : 1≤X^4 := one_le_pow₀ hX
    unfold workWidth
    nlinarith only [hp,hpow]
  have hws : stageCost (workWidth N W)≤2^162*X^14 := by
    unfold stageCost
    calc
      _≤2^96*(2^33*X^4)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2)
      _=2^162*X^8 := by ring
      _≤_ := Nat.mul_le_mul_left _ hx8
  unfold costBound
  change _≤2^170*X^14
  calc
    _≤(2^96+2^10+2+2^96+2^124+2^10+2+2^162+2^162)*X^14 := by
      nlinarith only [hs0,hs1,hm,he,hk,hws,h1]
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

theorem compiled_run (S : Finset ℕ) (N target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v) (hN : N.bits.length≤W) (hW : 4≤W)
    (hx : (v source).Valid) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hz : Clean s.val) (hp : Word s.val 640 N) :
    ∃ t : Store, (runPriced ((code target source).compile.next input tape)
      (2^170*(N+W+10)^14+1) s.val).finished=some (t.place (code target source).size) ∧
      (runPriced ((code target source).compile.next input tape)
      (2^170*(N+W+10)^14+1) s.val).instructions≤2^170*(N+W+10)^14 ∧
      Ready S (Function.update v target (result N (v source))) t ∧ Clean t.val ∧
      Word t.val 640 N ∧ BinaryPrecision.Frame (workspace S) s.val t.val ∧
      (result N (v source)).Valid ∧ (result N (v source)).value=(Profile.glueApprox (v source).value N).center := by
  obtain ⟨cost,t,ex,hcost,hr,hz',hp',hf⟩ := executes S N target source ht hs' v W hw hN hW hx
    input tape s hs hz hp
  have hb := hcost.trans (costBound_polynomial N W)
  have hout := ex.compiled_run (2^170*(N+W+10)^14+1) (by omega)
  exact ⟨t,hout.1,hout.2 ▸ hb,hr,hz',hp',hf,result_valid N (v source) hx,result_value N (v source) hx⟩

#print axioms costBound_polynomial
#print axioms compiled_run
end Maxwell.Continuum.RationalDataflow.Glue
