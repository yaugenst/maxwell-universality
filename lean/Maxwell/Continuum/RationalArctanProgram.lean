import Maxwell.Continuum.RationalArctanMachine

/-! Polynomial bit-operation evaluation of the actual arctangent prefix. -/

namespace Maxwell.Continuum.RationalArctan
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 1000000

def iterations (signs : ℕ→Sign) (n : ℕ) : ℕ→Code
  | 0 => .skip
  | r+1 => .seq (NatAssign.code (step (signs n) n)) (iterations signs (n+1) r)

def program (signs : ℕ→Sign) (N : ℕ) : Code :=
  .seq (NatAssign.code initialization) (iterations signs 0 N)

def costBound (N W : ℕ) : ℕ := (N+1)*2^60*(width N W+2)^2+1

theorem iterations_executes (a b : ℕ) (signs : ℕ→Sign) (n r N W : ℕ)
    (hn : n+r≤N) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready a b signs n s) :
    ∃ cost t, Executes input tape (iterations signs n r) cost s t ∧
      cost≤r*(2^60*(width N W+2)^2)+1 ∧ Ready a b signs (n+r) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  induction r generalizing n s with
  | zero => exact ⟨1,s,Executes.skip s,by simp,by simpa using hs,BinaryPrecision.Frame.refl _ _⟩
  | succ r ih =>
    obtain ⟨c,u,ec,hc,hu,hf⟩ := step_executes a b signs n N W (by omega) ha hb input tape s hs
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
      cost≤costBound N W ∧ Ready (v 610) (v 611) signs N t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c,u,ec,hc,hb,hu,hf⟩ := NatAssign.executes ids ids_ge initialization
    initialization_valid v input tape s hs hsc
  have hp := NatAssign.price_bound ids initialization initialization_valid v W hw
    (by simp [initialization,NatAssign.Instruction.literalWidth,hW])
  have hn : initialization.length=7 := by decide
  rw [hn] at hp
  have hwide : W≤width N W := by
    unfold width termWidth
    nlinarith only [Nat.zero_le (N*W),Nat.zero_le (N^2*W)]
  have hc' : c≤2^60*(width N W+2)^2 :=
    hc.trans (hp.trans (Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by omega) 2)))
  have hs' : Ready (v 610) (v 611) signs 0 u := by
    refine ⟨?_,hu⟩
    intro i hi
    simpa only [initialization_values v signs i hi] using hb i hi
  have hf' : BinaryPrecision.Frame workspace s.val u.val := by
    apply hf.mono
    simp [NatAssign.changes,initialization,NatAssign.Instruction.target,workspace]
    decide
  obtain ⟨d,t,ed,hd,ht,hg⟩ := iterations_executes (v 610) (v 611) signs 0 N N W
    (by omega) (hw 610 (by decide)) (hw 611 (by decide)) input tape u hs'
  refine ⟨c+d,t,ec.seq ed,?_,by simpa using ht,hf'.trans hg⟩
  unfold costBound
  nlinarith only [hc',hd]

theorem costBound_polynomial (N W : ℕ) :
    costBound N W≤2^66*(N+2)^5*(W+3)^2 := by
  have hw : width N W+2≤4*(N+2)^2*(W+3) := by
    unfold width termWidth
    nlinarith only [Nat.zero_le (N*W),Nat.zero_le (N^2*W)]
  have hs := Nat.pow_le_pow_left hw 2
  have h1 : 1≤(N+2)^5*(W+3)^2 := Nat.succ_le_of_lt (by positivity)
  calc
    _ ≤ (N+1)*2^60*(4*(N+2)^2*(W+3))^2+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hs) 1
    _ ≤ (N+2)*2^60*(4*(N+2)^2*(W+3))^2+1 := by gcongr; omega
    _ = 2^64*(N+2)^5*(W+3)^2+1 := by ring
    _ ≤ _ := by nlinarith only [h1]

theorem arctan_computes (v : ℕ→ℕ) (N W : ℕ) (hW : 1≤W)
    (hw : ∀ i ∈ ids, (v i).bits.length≤W) (hb : 0<v 611)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ (cost : ℕ) (t : Store),
      (runPriced ((program negativeSigns N).compile.next input tape) (costBound N W+1) s.val).finished=
        some (t.place (program negativeSigns N).size) ∧
      (runPriced ((program negativeSigns N).compile.next input tape) (costBound N W+1) s.val).instructions=cost ∧
      cost≤2^66*(N+2)^5*(W+3)^2 ∧ Ready (v 610) (v 611) negativeSigns N t ∧
      value (v 610) (v 611) negativeSigns N=
        Maxwell.Certificate.Elementary.arctanTaylor ((v 610:ℚ)/(v 611)) N := by
  obtain ⟨cost,t,he,hc,ht,_⟩ := program_executes v negativeSigns N W hW hw input tape s hs hsc
  obtain ⟨hrun,hcost⟩ := he.compiled_run (costBound N W+1) (by omega)
  exact ⟨cost,t,hrun,hcost,hc.trans (costBound_polynomial N W),ht,(arctanTaylor_eq _ _ hb _).symm⟩

#print axioms program_executes
#print axioms arctan_computes

end Maxwell.Continuum.RationalArctan
