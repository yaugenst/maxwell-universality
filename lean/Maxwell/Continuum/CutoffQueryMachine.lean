import Maxwell.Continuum.CutoffQueryMeaning

/-! Executable exact cutoff queries on the stored finite coefficient table.
Counter initialization, every array read, comparison, division, and multiplication
are included in the charged program. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] polynomialPlanEvaluate polynomialPlanCode cutoffQueryPlan

def cutoffQueryCode : Code :=
  .seq (WordReplace.code 201 206) (polynomialPlanCode cutoffQueryPlan)

def cutoffQueryCost (n W wordLength : ℕ) : ℕ :=
  15*wordLength+21+polynomialPlanCost n W 42

theorem cutoffQuery_computes (N : ℕ) (a : Table (Profile.profileDegree N))
    (hdata : ∀ i, a.get i=antiderivativeCoefficient N i)
    (W : ℕ) (hW : 3≤W) (hcoeffWidth : 2^65*(N+1)^4≤W) (hmeta : a.MetadataWidth W)
    (v : ℕ→Parts) (hw : WidthBank querySlots W v) (hg : Good querySlots v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=Profile.profileDegree N)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin) (hblank : Blank s.val 206)
    (hs : Ready querySlots v s) (ha : a.Ready s) :
    ∃ t output,
      (runPriced (cutoffQueryCode.compile.next input tape)
        (cutoffQueryCost (Profile.profileDegree N) W xs.length+1) s.val).finished=
          some (t.place cutoffQueryCode.size) ∧
      (runPriced (cutoffQueryCode.compile.next input tape)
        (cutoffQueryCost (Profile.profileDegree N) W xs.length+1) s.val).instructions≤
          cutoffQueryCost (Profile.profileDegree N) W xs.length ∧
      Ready querySlots output t ∧ Good querySlots output ∧ a.Ready t ∧
      WidthBank querySlots (polynomialPlanWidth (Profile.profileDegree N) W 42) output ∧
      (output 16).value=chiCenter (fun i : Fin 3 => (v (10+i.val)).value) N := by
  have width (i : Fin (Profile.profileDegree N)) : (a.get i).Width W := by
    rw [hdata i]
    exact (antiderivativeCoefficient_width_polynomial N i).mono hcoeffWidth
  have valid (i : Fin (Profile.profileDegree N)) : (a.get i).Valid := by
    rw [hdata i]
    exact antiderivativeCoefficient_valid N i
  have values (i : Fin (Profile.profileDegree N)) :
      (a.get i).value=(antiderivativeCoefficient N i).value := congrArg Parts.value (hdata i)
  have empty : BankArray.Word s.val 206 [] := by
    obtain ⟨o,ho⟩ := hblank
    exact ⟨o,by simpa only [BitTape.shifted_nil] using ho⟩
  obtain ⟨s0,e0,saved0,f0⟩ := WordReplace.executes 201 206 (by decide)
    input tape xs [] s ⟨origin,hcount⟩ empty
  have outside206 : 206∉workspace querySlots := outside_workspace querySlots 206 (by decide)
  have bank0 := hs.wordReplace_frame outside206 f0
  have array0 := ha.copy_frame (Or.inr rfl) f0
  have count0 : BankArray.Word s0.val 201 xs :=
    ⟨origin,(f0.2.2.2.2.2.1 201 (by decide)).trans hcount⟩
  obtain ⟨cost,t,_,he,hcost,hready,harray,_,_,_,hgood,hwidth⟩ :=
    polynomialPlan_executes a querySlots (by decide) (by decide) (by decide)
      cutoffQueryPlan cutoffQueryPlan_valid W (by omega) (cutoffQueryPlan_literals W hW)
      hmeta width valid v hw hg (cutoffQueryPlan_admissible N a values valid v hg)
      input tape xs xs hlen hlen s0 hn saved0 count0 bank0 array0
  have total := e0.seq he
  have bound : (6*([] : List Bool).length+15*xs.length+21)+cost≤
      cutoffQueryCost (Profile.profileDegree N) W xs.length := by
    unfold cutoffQueryCost
    rw [cutoffQueryPlan_length] at hcost
    simp only [List.length_nil]
    omega
  obtain ⟨hrun,hsteps⟩ := total.compiled_run
    (cutoffQueryCost (Profile.profileDegree N) W xs.length+1) (by omega)
  refine ⟨t,polynomialPlanEvaluate a cutoffQueryPlan v,hrun,hsteps ▸ bound,
    hready,hgood,harray,?_,cutoffQueryPlan_value N a values valid v hg⟩
  simpa only [cutoffQueryPlan_length] using hwidth

theorem cutoffQueryCost_polynomial (n W wordLength : ℕ) (hlen : wordLength≤W) :
    cutoffQueryCost n W wordLength≤2^1000*(n+1)^87*(W+2)^2 := by
  let A := polynomialPlanWidth n W 42
  have hp : 1≤(1024*(n+1))^42 := one_le_pow₀ (by omega)
  have hA : 2≤A := by dsimp [A,polynomialPlanWidth]; nlinarith
  have ha : A+2≤2*A := by omega
  have hs := Nat.pow_le_pow_left ha 2
  have hconst : 43*2^132*4*1024^84≤(2:ℕ)^990 := by norm_num
  have hpower : 43*2^132*(n+1)^3*(2*A)^2=
      (43*2^132*4*1024^84)*(n+1)^87*(W+2)^2 := by
    dsimp [A,polynomialPlanWidth]
    simp only [mul_pow,← pow_mul]
    ring
  have hmain : polynomialPlanCost n W 42≤2^990*(n+1)^87*(W+2)^2 := by
    have heq : polynomialPlanCost n W 42=43*2^132*(n+1)^3*(A+2)^2 := by
      unfold polynomialPlanCost PolynomialStage.costBound
      change 43*(2^132*(n+1)^3*(A+2)^2)=_
      ring
    rw [heq]
    calc
      _ ≤ 43*2^132*(n+1)^3*(2*A)^2 := Nat.mul_le_mul_left _ hs
      _ = _ := hpower
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hconst)
  have hbase : 1≤(n+1)^87 := one_le_pow₀ (by omega)
  have hW2 : W+1≤(W+2)^2 := by nlinarith
  have hsize := Nat.mul_le_mul_right ((W+2)^2) hbase
  have hcounter : 15*wordLength+21≤64*(n+1)^87*(W+2)^2 := by
    nlinarith only [hlen,hW2,hsize]
  unfold cutoffQueryCost
  nlinarith only [hmain,hcounter,Nat.zero_le ((n+1)^87*(W+2)^2)]

theorem cutoffQueryCost_precision (N W wordLength : ℕ) (hlen : wordLength≤W) :
    cutoffQueryCost (Profile.profileDegree N) W wordLength≤
      2^3700*(N+1)^174*(W+2)^2 := by
  have hd := Profile.profileDegree_bound N
  have hp : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hdp : Profile.profileDegree N+1≤2^31*(N+1)^2 := by nlinarith
  have hh := Nat.pow_le_pow_left hdp 87
  have hm := Nat.mul_le_mul_right ((W+2)^2) (Nat.mul_le_mul_left (2^1000) hh)
  have he : 2^1000*(2^31*(N+1)^2)^87*(W+2)^2=
      (2:ℕ)^3697*(N+1)^174*(W+2)^2 := by
    simp only [mul_pow,← pow_mul]
    ring
  rw [he] at hm
  apply (cutoffQueryCost_polynomial _ W wordLength hlen).trans (hm.trans _)
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by decide)))

#print axioms cutoffQuery_computes
#print axioms cutoffQueryCost_precision
end Maxwell.Continuum.Calibration.RawCutoff
