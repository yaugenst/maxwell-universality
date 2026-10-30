import Maxwell.Continuum.RationalTaylorMachine
import Maxwell.Cost.Structured.Correctness

/-! Exact finite Taylor evaluation with charged integer arithmetic.
The signed coefficient stream is part of the generated finite program;
the rational argument is read from the two stored input words. -/

namespace Maxwell.Continuum.RationalTaylor
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 1000000

def iterations (signs : ℕ → Sign) (n : ℕ) : ℕ → Code
  | 0 => .skip
  | r+1 => .seq (NatAssign.code (step (signs (n+1)) n)) (iterations signs (n+1) r)

def program (signs : ℕ → Sign) (N : ℕ) : Code :=
  .seq (NatAssign.code (initialization (signs 0))) (iterations signs 0 N)

def costBound (N W : ℕ) : ℕ := (N+1)*2^40*(width N W+2)^2+1

theorem iterations_executes (a b : ℕ) (signs : ℕ → Sign) (n r N W : ℕ)
    (hn : n+r≤N) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready a b signs n s) :
    ∃ cost t, Executes input tape (iterations signs n r) cost s t ∧
      cost ≤ r*(2^40*(width N W+2)^2)+1 ∧ Ready a b signs (n+r) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  induction r generalizing n s with
  | zero =>
    exact ⟨1,s,Executes.skip s,by simp,by simpa using hs,BinaryPrecision.Frame.refl _ _⟩
  | succ r ih =>
    obtain ⟨c,u,ec,hc,hu,hf⟩ := step_executes a b signs n N W (by omega)
      ha hb input tape s hs
    obtain ⟨d,t,ed,hd,ht,hg⟩ := ih (n+1) (by omega) u hu
    refine ⟨c+d,t,ec.seq ed,?_,?_,hf.trans hg⟩
    · nlinarith only [hc,hd]
    · convert ht using 1
      omega

theorem program_executes (v : ℕ→ℕ) (signs : ℕ→Sign) (N W : ℕ) (hW : 1≤W)
    (hw : ∀ i ∈ ids, (v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (program signs N) cost s t ∧
      cost ≤ costBound N W ∧ Ready (v 600) (v 601) signs N t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c,u,ec,hc,hb,hu,hf⟩ := NatAssign.executes ids ids_ge (initialization (signs 0))
    (initialization_valid _) v input tape s hs hsc
  have hp := NatAssign.price_bound ids (initialization (signs 0)) (initialization_valid _)
    v W hw (by cases signs 0 <;> simp [initialization,NatAssign.Instruction.literalWidth,hW,Sign.positive,Sign.negative])
  have hn : (initialization (signs 0)).length=5 := by simp [initialization]
  rw [hn] at hp
  have hwide : W≤width N W := by unfold width; nlinarith
  have hc' : c≤2^40*(width N W+2)^2 := by
    apply hc.trans (hp.trans _)
    exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by omega) 2)
  have hs' : Ready (v 600) (v 601) signs 0 u := by
    refine ⟨?_,hu⟩
    intro i hi
    simpa only [initialization_values v signs i hi] using hb i hi
  have hf' : BinaryPrecision.Frame workspace s.val u.val := by
    apply hf.mono
    simp [NatAssign.changes,initialization,NatAssign.Instruction.target,workspace]
    decide
  obtain ⟨d,t,ed,hd,ht,hg⟩ := iterations_executes (v 600) (v 601) signs 0 N N W
    (by omega) (hw 600 (by decide)) (hw 601 (by decide)) input tape u hs'
  refine ⟨c+d,t,ec.seq ed,?_,by simpa using ht,hf'.trans hg⟩
  unfold costBound
  nlinarith only [hc',hd]

theorem costBound_polynomial (N W : ℕ) :
    costBound N W ≤ 2^44*(N+2)^5*(W+3)^2 := by
  have hw0 : W+N+3≤(N+2)*(W+3) := by nlinarith only [Nat.zero_le (N*W)]
  have hw1 : width N W ≤ (N+2)^2*(W+3) := by
    calc
      _ ≤ (N+2)*((N+2)*(W+3)) := Nat.mul_le_mul (by omega) hw0
      _ = _ := by ring
  have hw2 : 2≤(N+2)^2*(W+3) := by
    have hq : 1≤(N+2)^2 := one_le_pow₀ (by omega)
    nlinarith only [hq]
  have hw : width N W+2 ≤ 2*(N+2)^2*(W+3) := by
    nlinarith only [hw1,hw2]
  have hs := Nat.pow_le_pow_left hw 2
  have h1 : 1≤(N+2)^5*(W+3)^2 := Nat.succ_le_of_lt (by positivity)
  calc
    _ ≤ (N+1)*2^40*(2*(N+2)^2*(W+3))^2+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hs) 1
    _ ≤ (N+2)*2^40*(2*(N+2)^2*(W+3))^2+1 := by gcongr; omega
    _ = 2^42*(N+2)^5*(W+3)^2+1 := by ring
    _ ≤ _ := by nlinarith only [h1]

/-- The compiled finite Boolean program terminates and leaves the exact
signed Taylor numerator parts and denominator on its output tapes. -/
theorem program_computes (v : ℕ→ℕ) (signs : ℕ→Sign) (N W : ℕ) (hW : 1≤W)
    (hw : ∀ i ∈ ids, (v i).bits.length≤W) (hb : 0<v 601)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ (cost : ℕ) (t : Store),
      (runPriced ((program signs N).compile.next input tape) (costBound N W+1) s.val).finished =
        some (t.place (program signs N).size) ∧
      (runPriced ((program signs N).compile.next input tape) (costBound N W+1) s.val).instructions=cost ∧
      cost≤2^44*(N+2)^5*(W+3)^2 ∧
      Word t.val 602 (numerator (v 600) (v 601) (fun k => (signs k).positive) N) ∧
      Word t.val 603 (numerator (v 600) (v 601) (fun k => (signs k).negative) N) ∧
      Word t.val 604 (denominator (v 601) N) ∧
      value (v 600) (v 601) signs N =
        ∑ k ∈ Finset.range (N+1), (signs k).value*((v 600:ℚ)/(v 601))^k/(k.factorial:ℚ) := by
  obtain ⟨cost,t,he,hc,ht,_⟩ := program_executes v signs N W hW hw input tape s hs hsc
  obtain ⟨hrun,hcost⟩ := he.compiled_run (costBound N W+1) (by omega)
  refine ⟨cost,t,hrun,hcost,hc.trans (costBound_polynomial N W),?_,?_,?_,value_sum _ _ hb _ _⟩
  · simpa [values] using ht.bank 602 (by decide)
  · simpa [values] using ht.bank 603 (by decide)
  · simpa [values] using ht.bank 604 (by decide)

#print axioms program_executes
#print axioms program_computes

end Maxwell.Continuum.RationalTaylor
