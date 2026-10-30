import Maxwell.Continuum.RationalTaylorRuntimeLoop

/-! Fixed-code exponential/sine/cosine evaluators, with runtime term counts
and a complete charged execution bound. -/
namespace Maxwell.Continuum.RationalTaylor.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def positiveCycle : Cycle := fun _ => .plus
def negativeCycle : Cycle := ![.plus,.minus,.plus,.minus]
def cosineCycle : Cycle := ![.plus,.zero,.minus,.zero]
def sineCycle : Cycle := ![.zero,.plus,.zero,.minus]

theorem positiveCycle_signs : cycleSigns positiveCycle=positiveSigns := rfl
theorem negativeCycle_signs : cycleSigns negativeCycle=negativeSigns := by
  funext n
  have h : n%4<4 := Nat.mod_lt _ (by decide)
  interval_cases hm : n%4
  all_goals have h2 : n%2=(n%4)%2 := by omega
  all_goals simp [cycleSigns,negativeCycle,negativeSigns,hm,h2]
theorem cosineCycle_signs : cycleSigns cosineCycle=cosineSigns := by
  funext n
  have h : n%4<4 := Nat.mod_lt _ (by decide)
  interval_cases hm : n%4 <;> simp [cycleSigns,cosineCycle,cosineSigns,hm]
theorem sineCycle_signs : cycleSigns sineCycle=sineSigns := by
  funext n
  have h : n%4<4 := Nat.mod_lt _ (by decide)
  interval_cases hm : n%4 <;> simp [cycleSigns,sineCycle,sineSigns,hm]

theorem costBound_polynomial (N W L : ℕ) :
    costBound N W L≤2^50*(N+2)^5*(W+L+3)^2 := by
  have hw0 : W+N+3≤(N+2)*(W+3) := by nlinarith only [Nat.zero_le (N*W)]
  have hw1 : width N W≤(N+2)^2*(W+3) := by
    calc
      _ ≤ (N+2)*((N+2)*(W+3)) := Nat.mul_le_mul (by omega) hw0
      _ = _ := by ring
  have htwo : 2≤(N+2)^2*(W+3) := by
    have hq : 1≤(N+2)^2 := one_le_pow₀ (by omega)
    nlinarith only [hq]
  have hw2 : width N W+2≤2*(N+2)^2*(W+3) := by nlinarith only [hw1,htwo]
  have hs := Nat.pow_le_pow_left hw2 2
  have hN : N+1≤(N+2)^5 := by
    exact (by omega : N+1≤N+2).trans (Nat.le_self_pow (by decide) (N+2))
  have hW : W+L+3≤(W+L+3)^2 := Nat.le_self_pow (by decide) _
  have hbase : 1≤(N+2)^5*(W+L+3)^2 := Nat.succ_le_of_lt (by positivity)
  have hNL : (N+1)*(13*L+15)≤15*((N+2)^5*(W+L+3)^2) := by
    calc
      _ ≤ (N+2)^5*(15*(W+L+3)^2) := Nat.mul_le_mul hN (by omega)
      _ = _ := by ring
  have hinit : 2^44*(W+2)^2≤2^44*((N+2)^5*(W+L+3)^2) := by
    apply Nat.mul_le_mul_left
    calc
      _ ≤ (W+L+3)^2 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (N+2)^5*(W+L+3)^2 := Nat.le_mul_of_pos_left _ (by positivity)
  have hmain : N*(2^44*(width N W+2)^2)≤2^46*((N+2)^5*(W+L+3)^2) := by
    calc
      _ ≤ (N+2)*(2^44*(2*(N+2)^2*(W+3))^2) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hs)
      _ = 2^46*((N+2)^5*(W+3)^2) := by ring
      _ ≤ _ := Nat.mul_le_mul_left (2^46) (Nat.mul_le_mul_left ((N+2)^5)
        (Nat.pow_le_pow_left (by omega : W+3≤W+L+3) 2))
  have hn : N≤(N+2)^5*(W+L+3)^2 := by
    exact (by omega : N≤(N+2)^5).trans (Nat.le_mul_of_pos_right _ (by positivity))
  calc
    _ = 2^44*(W+2)^2+4+(N+1)*(13*L+15)+N*(2^44*(width N W+2)^2)+6*N := by
      unfold costBound loopCost
      ring
    _ ≤ (2^44+15+2^46+10)*((N+2)^5*(W+L+3)^2) := by omega
    _ ≤ 2^50*((N+2)^5*(W+L+3)^2) := Nat.mul_le_mul_right _ (by norm_num)
    _ = _ := by ring

theorem program_computes (cycle : Cycle) (countTape N W : ℕ) (v : ℕ→ℕ)
    (hcount : countTape∉ids) (hc4 : 4≤countTape) (hW : 1≤W)
    (hw : ∀i∈ids,(v i).bits.length≤W) (hb : 0<v 601)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue word=N) (hword : s.val.tapes countTape=BitTape.shifted word origin)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,
      (runPriced ((program cycle countTape).compile.next input tape) (costBound N W word.length+1) s.val).finished=
        some (t.place (program cycle countTape).size) ∧
      (runPriced ((program cycle countTape).compile.next input tape) (costBound N W word.length+1) s.val).instructions=cost ∧
      cost≤2^50*(N+2)^5*(W+word.length+3)^2 ∧
      Ready (v 600) (v 601) (cycleSigns cycle) N t ∧
      value (v 600) (v 601) (cycleSigns cycle) N=
        ∑k∈Finset.range (N+1),(cycleSigns cycle k).value*((v 600:ℚ)/(v 601))^k/(k.factorial:ℚ) := by
  obtain ⟨cost,t,_,he,hc,ht,_,_,_⟩ := program_executes cycle countTape N W v hcount hc4 hW hw
    input tape word origin s hn hword hs hz
  have hout := he.compiled_run (costBound N W word.length+1) (by omega)
  exact ⟨cost,t,hout.1,hout.2,hc.trans (costBound_polynomial N W word.length),ht.data,
    value_sum _ _ hb _ _⟩

/-- The code is independent of every runtime numeric parameter. -/
theorem program_size_bound (cycle : Cycle) (countTape : ℕ) : (program cycle countTape).size≤2^20 := by
  have hs (s : Sign) : (NatAssign.code (step s)).size≤2^16 := by cases s <;> decide
  have hi : (NatAssign.code (initialization cycle)).size≤2^16 := by
    cases h : cycle 0 <;>
      simp only [initialization,h,RationalTaylor.initialization,Sign.positive,Sign.negative,
        ite_true,Bool.false_eq_true,ite_false] <;> decide
  have hsize : (program cycle countTape).size=
      (NatAssign.code (initialization cycle)).size+
      (NatAssign.code (step (cycle 0))).size+(NatAssign.code (step (cycle 1))).size+
      (NatAssign.code (step (cycle 2))).size+(NatAssign.code (step (cycle 3))).size+2*Counter.program.code.length+16 := by
    simp only [program,initCode,loop,RationalDataflow.countedProgram,CountedShifted.code,
      Counted.code,Counted.test,cycleStep,cycleSelect,cycleAdvance,Code.size,Code.atom,
      Counter.programOn,BitRAM.renameTapes,List.length_map,List.length_cons,List.length_nil]
    omega
  have hc : Counter.program.code.length≤1000 := by decide
  have h0 := hs (cycle 0)
  have h1 := hs (cycle 1)
  have h2 := hs (cycle 2)
  have h3 := hs (cycle 3)
  omega

#print axioms program_computes
#print axioms program_size_bound
end Maxwell.Continuum.RationalTaylor.Runtime
