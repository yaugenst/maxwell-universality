import Maxwell.Continuum.PhaseRuntimeDataflowExecution

/-! Uniform charged bit time for shared fixed-code phase evaluations. -/
namespace Maxwell.Continuum.RationalDataflow.Phase.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem costBound_polynomial (Q N W : ℕ) : costBound Q N W≤2^322*(Q+N+W+12)^14 := by
  let X := Q+N+W+12
  have hX : 1≤X := by dsimp [X];omega
  have h1 : 1≤X^14 := one_le_pow₀ hX
  have h2 : X^2≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have h8 : X^8≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have hself : X≤X^14 := Nat.le_self_pow (by decide) _
  have hpre : stageCost W≤2^180*X^14 := by
    unfold stageCost
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp [X];omega : W+2≤X) 2).trans h2)
  have hpre' : stageCost (W+1)≤2^180*X^14 := by
    unfold stageCost
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp [X];omega : W+1+2≤X) 2).trans h2)
  have hmag : 300*(2*W+4)≤2^10*X^14 := by
    have hw : W+2≤X := by dsimp [X];omega
    omega
  have hcore : PhaseMachine.Runtime.costBound Q N (W+1)≤2^230*X^14 :=
    (PhaseMachine.Runtime.costBound_polynomial Q N (W+1)).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by unfold PhaseMachine.sizeParameter;dsimp [X];omega) 14))
  have hww : workWidth Q N W+2≤2^69*X^4 := by
    have hx : 1≤X^4 := one_le_pow₀ hX
    unfold workWidth
    change 2^68*X^4+2≤2^69*X^4
    omega
  have hfinish : stageCost (workWidth Q N W)≤2^318*X^14 := by
    calc
      _≤2^180*(2^69*X^4)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hww 2)
      _=2^318*X^8 := by ring
      _≤_ := Nat.mul_le_mul_left _ h8
  have hall := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add hpre hmag) (Nat.mul_le_mul_left 2 h1)) hpre') hcore) hfinish
  change costBound Q N W≤_ at hall
  apply hall.trans
  change _≤2^322*X^14
  calc
    _=(2^180+2^10+2+2^180+2^230+2^318)*X^14 := by simp only [Nat.add_mul]
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

theorem compiled_run (S : Finset ℕ) (base : RationalTaylor.Runtime.Cycle) (Q N target source : ℕ)
    (ht : target∈S) (hs' : source∈S) (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s)
    (hz : Clean s.val) (hq : Word s.val 652 Q) (hn : Word s.val 653 N) :
    ∃t : Store,
      (runPriced ((code base target source).compile.next input tape) (2^322*(Q+N+W+12)^14+1) s.val).finished=
        some (t.place (code base target source).size) ∧
      (runPriced ((code base target source).compile.next input tape) (2^322*(Q+N+W+12)^14+1) s.val).instructions≤
        2^322*(Q+N+W+12)^14 ∧
      Ready S (Function.update v target (Phase.result (RationalTaylor.Runtime.cycleSigns base) Q N (v source))) t ∧
      Clean t.val ∧ Word t.val 652 Q ∧ Word t.val 653 N ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c,t,e,hc,ready,clean,qword,nword,ft⟩ := executes S base Q N target source ht hs' v W hw hQ hN hW
    input tape s hs hz hq hn
  have hbnd := hc.trans (costBound_polynomial Q N W)
  obtain ⟨hrun,hsteps⟩ := e.compiled_run (2^322*(Q+N+W+12)^14+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hbnd,ready,clean,qword,nword,ft⟩

#print axioms compiled_run
end Maxwell.Continuum.RationalDataflow.Phase.Runtime
