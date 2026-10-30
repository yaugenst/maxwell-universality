import Maxwell.Continuum.MachinRuntimeSetup

/-! Uniform code size and charged polynomial execution for the runtime
Machin evaluator. Its only precision input is a stored natural word. -/
namespace Maxwell.Continuum.Machin.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem callCost_polynomial (N : ℕ) : callCost N≤2^97*(N+1)^7 := by
  have hb := nat_bits_le_self (N+6)
  have hc := nat_bits_le_self (2*(N+6)+1)
  have hn : N+6+2≤8*(N+1) := by omega
  have hsmall : 21*(N+6).bits.length+6*(2*(N+6)+1).bits.length+60≤2^9*(N+1)^7 := by
    have hp : N+1≤(N+1)^7 := Nat.le_self_pow (by decide) _
    omega
  have hmain' : RationalArctan.Runtime.costBound (N+6) 8 (N+6).bits.length≤2^96*(N+1)^7 := by
    have hi' : 8+(N+6).bits.length+3≤17*(N+1) := by omega
    calc
      _≤2^72*(N+6+2)^5*(8+(N+6).bits.length+3)^2 :=
        RationalArctan.Runtime.costBound_polynomial _ _ _
      _≤2^72*(8*(N+1))^5*(17*(N+1))^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 5)) (Nat.pow_le_pow_left hi' 2)
      _=(2^72*8^5*17^2)*(N+1)^7 := by ring
      _≤_ := Nat.mul_le_mul_right _ (by norm_num)
  calc
    _=RationalArctan.Runtime.costBound (N+6) 8 (N+6).bits.length+
        (21*(N+6).bits.length+6*(2*(N+6)+1).bits.length+60) := by
      unfold callCost RationalArctan.Runtime.cleanCost
      ring
    _≤2^96*(N+1)^7+2^9*(N+1)^7 := Nat.add_le_add hmain' hsmall
    _=(2^96+2^9)*(N+1)^7 := by ring
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

theorem costBound_polynomial (N : ℕ) : costBound N≤2^120*(N+1)^7 := by
  have hs : 3*stageCost N≤2^112*(N+1)^5 :=
    (by unfold Machin.costBound;omega : 3*stageCost N≤Machin.costBound N).trans
      (Machin.costBound_polynomial N)
  have hX : 1≤N+1 := by omega
  have hp : (N+1)^5≤(N+1)^7 := Nat.pow_le_pow_right hX (by decide)
  have h2 : (N+1)^2≤(N+1)^7 := Nat.pow_le_pow_right hX (by decide)
  have h1 : N+1≤(N+1)^7 := Nat.le_self_pow (by decide) _
  have hstage := hs.trans (Nat.mul_le_mul_left _ hp)
  have hc := callCost_polynomial N
  have hsetup : 2^30*(N+8)^2≤2^36*(N+1)^7 := by
    calc
      _≤2^30*(8*(N+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=2^36*(N+1)^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ h2
  have hb := nat_bits_le_self (N+6)
  have hclear : 6*(N+6).bits.length+4≤2^6*(N+1)^7 := by omega
  calc
    _=2^30*(N+8)^2+3*stageCost N+2*callCost N+(6*(N+6).bits.length+4) := by
      unfold costBound coreCost
      ring
    _≤2^36*(N+1)^7+2^112*(N+1)^7+2*(2^97*(N+1)^7)+2^6*(N+1)^7 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsetup hstage) (Nat.mul_le_mul_left 2 hc)) hclear
    _=(2^36+2^112+2^98+2^6)*(N+1)^7 := by ring
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

theorem program_computes (N : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds (fun _ => 0) s.val) (hz : NatAssign.Scratch s.val)
    (ha : InputReady N s.val) :
    ∃t : Store, (runPriced (program.compile.next input tape) (2^120*(N+1)^7+1) s.val).finished=
        some (t.place program.size) ∧
      (runPriced (program.compile.next input tape) (2^120*(N+1)^7+1) s.val).instructions≤2^120*(N+1)^7 ∧
      Word t.val 623 (numeratorPositive N) ∧ Word t.val 624 (numeratorNegative N) ∧
      Word t.val 625 (commonDenominator N) ∧
      (Maxwell.Certificate.Elementary.piApprox N).center=
        ((numeratorPositive N:ℚ)-numeratorNegative N)/commonDenominator N ∧
      InputReady N t.val := by
  obtain ⟨cost,t,he,hc,bt,_,aux,_⟩ := program_executes N input tape s hs hz ha
  have hb := hc.trans (costBound_polynomial N)
  obtain ⟨hrun,hsteps⟩ := he.compiled_run (2^120*(N+1)^7+1) (by omega)
  refine ⟨t,hrun,hsteps ▸ hb,?_,?_,?_,piApprox_center N,aux⟩
  · simpa only [finalValues,(combine_values N).1] using bt 623 (by decide)
  · simpa only [finalValues,(combine_values N).2.1] using bt 624 (by decide)
  · simpa only [finalValues,(combine_values N).2.2] using bt 625 (by decide)

#print axioms program_computes
end Maxwell.Continuum.Machin.Runtime
