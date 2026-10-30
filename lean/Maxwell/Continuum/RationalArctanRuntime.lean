import Maxwell.Continuum.RationalArctanRuntimeLoop

/-! Actual fixed-code arctangent execution and uniform resource bounds. -/
namespace Maxwell.Continuum.RationalArctan.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem costBound_polynomial (N W L : ℕ) :
    costBound N W L≤2^72*(N+2)^5*(W+L+3)^2 := by
  have hw : RationalArctan.width N W+2≤4*(N+2)^2*(W+3) := by
    unfold RationalArctan.width termWidth
    nlinarith only [Nat.zero_le (N*W),Nat.zero_le (N^2*W)]
  have hs := Nat.pow_le_pow_left hw 2
  have hN : N+1≤(N+2)^5 :=
    (by omega : N+1≤N+2).trans (Nat.le_self_pow (by decide) (N+2))
  have hW : W+L+3≤(W+L+3)^2 := Nat.le_self_pow (by decide) _
  have hbase : 1≤(N+2)^5*(W+L+3)^2 := Nat.succ_le_of_lt (by positivity)
  have hNL : (N+1)*(13*L+15)≤15*((N+2)^5*(W+L+3)^2) := by
    calc
      _ ≤ (N+2)^5*(15*(W+L+3)^2) := Nat.mul_le_mul hN (by omega)
      _ = _ := by ring
  have hinit : 2^48*(W+2)^2≤2^48*((N+2)^5*(W+L+3)^2) := by
    apply Nat.mul_le_mul_left
    calc
      _ ≤ (W+L+3)^2 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (N+2)^5*(W+L+3)^2 := Nat.le_mul_of_pos_left _ (by positivity)
  have hmain : N*(2^64*(RationalArctan.width N W+2)^2)≤2^68*((N+2)^5*(W+L+3)^2) := by
    calc
      _ ≤ (N+2)*(2^64*(4*(N+2)^2*(W+3))^2) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hs)
      _ = 2^68*((N+2)^5*(W+3)^2) := by ring
      _ ≤ _ := Nat.mul_le_mul_left (2^68) (Nat.mul_le_mul_left ((N+2)^5)
        (Nat.pow_le_pow_left (by omega : W+3≤W+L+3) 2))
  have hn : N≤(N+2)^5*(W+L+3)^2 :=
    (by omega : N≤(N+2)^5).trans (Nat.le_mul_of_pos_right _ (by positivity))
  calc
    _ = 2^48*(W+2)^2+2+(N+1)*(13*L+15)+N*(2^64*(RationalArctan.width N W+2)^2)+3*N := by
      unfold costBound loopCost
      ring
    _ ≤ (2^48+15+2^68+5)*((N+2)^5*(W+L+3)^2) := by omega
    _ ≤ 2^72*((N+2)^5*(W+L+3)^2) := Nat.mul_le_mul_right _ (by norm_num)
    _ = _ := by ring

theorem program_computes (countTape N W : ℕ) (v : ℕ→ℕ)
    (hcount : countTape∉ids) (hc4 : 4≤countTape) (hW : 2≤W) (hw : ∀i∈ids,(v i).bits.length≤W)
    (hb : 0<v 611) (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue word=N) (hword : s.val.tapes countTape=BitTape.shifted word origin)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,
      (runPriced ((program countTape).compile.next input tape) (costBound N W word.length+1) s.val).finished=
        some (t.place (program countTape).size) ∧
      (runPriced ((program countTape).compile.next input tape) (costBound N W word.length+1) s.val).instructions=cost ∧
      cost≤2^72*(N+2)^5*(W+word.length+3)^2 ∧ Ready (v 610) (v 611) N t ∧
      RationalArctan.value (v 610) (v 611) negativeSigns N=
        Maxwell.Certificate.Elementary.arctanTaylor ((v 610:ℚ)/(v 611)) N := by
  obtain ⟨cost,t,_,he,hc,ht,_,_,_⟩ := program_executes countTape N W v hcount hc4 hW hw
    input tape word origin s hn hword hs hz
  have hout := he.compiled_run (costBound N W word.length+1) (by omega)
  exact ⟨cost,t,hout.1,hout.2,hc.trans (costBound_polynomial N W word.length),ht.data,
    (arctanTaylor_eq _ _ hb _).symm⟩

theorem program_size_bound (countTape : ℕ) : (program countTape).size≤2^20 := by
  have hplus : (NatAssign.code (step .plus)).size≤2^16 := by decide
  have hminus : (NatAssign.code (step .minus)).size≤2^16 := by decide
  have hi : (NatAssign.code initialization).size≤2^16 := by decide
  have hc : Counter.program.code.length≤1000 := by decide
  have hsize : (program countTape).size=(NatAssign.code initialization).size+
      (NatAssign.code (step .plus)).size+(NatAssign.code (step .minus)).size+
        2*Counter.program.code.length+10 := by
    simp only [program,initCode,loop,RationalDataflow.countedProgram,CountedShifted.code,
      Counted.code,Counted.test,cycleStep,cycleSelect,Code.size,Code.atom,
      Counter.programOn,BitRAM.renameTapes,List.length_map,List.length_cons,List.length_nil]
    omega
  omega

#print axioms program_computes
#print axioms program_size_bound
end Maxwell.Continuum.RationalArctan.Runtime
