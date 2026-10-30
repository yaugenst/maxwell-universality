import Maxwell.Continuum.RationalDataflowPolynomialStage

/-! Composition of a fixed query schedule. The emitted schedule is independent
of polynomial degree; only the existing stored-array traversal has growing length. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

def polynomialPlanCode : List PolynomialStage→Code
  | [] => .skip
  | op::rest => .seq op.code (polynomialPlanCode rest)

def polynomialPlanEvaluate {n : ℕ} (a : Table n) : List PolynomialStage→(ℕ→Parts)→(ℕ→Parts)
  | [],v => v
  | op::rest,v => polynomialPlanEvaluate a rest (op.evaluate a v)

def PolynomialPlanAdmissible {n : ℕ} (a : Table n) : List PolynomialStage→(ℕ→Parts)→Prop
  | [],_ => True
  | op::rest,v => op.Admissible v ∧ PolynomialPlanAdmissible a rest (op.evaluate a v)

def polynomialPlanWidth (n W steps : ℕ) : ℕ := (1024*(n+1))^steps*(W+2)
def polynomialPlanCost (n W steps : ℕ) : ℕ :=
  (steps+1)*PolynomialStage.costBound n (polynomialPlanWidth n W steps)

theorem polynomialPlanWidth_ge (n W steps : ℕ) : W≤polynomialPlanWidth n W steps := by
  have hp : 1≤(1024*(n+1))^steps := one_le_pow₀ (by omega)
  unfold polynomialPlanWidth
  nlinarith

theorem polynomialPlanWidth_step (n W steps : ℕ) :
    polynomialPlanWidth n (PolynomialStage.width n W) steps≤polynomialPlanWidth n W (steps+1) := by
  have hh : PolynomialStage.width n W+2≤1024*(n+1)*(W+2) := by
    unfold PolynomialStage.width
    nlinarith
  have hm := Nat.mul_le_mul_left ((1024*(n+1))^steps) hh
  simpa only [polynomialPlanWidth,pow_succ,Nat.mul_assoc] using hm

theorem PolynomialStage.LiteralsFit.mono {op : PolynomialStage} {W B : ℕ}
    (h : op.LiteralsFit W) (hWB : W≤B) : op.LiteralsFit B := by
  cases op
  · exact Instruction.LiteralFits.mono h hWB
  · trivial
  · trivial

theorem PolynomialStage.costBound_mono (n : ℕ) {W B : ℕ} (hWB : W≤B) :
    costBound n W≤costBound n B := by unfold costBound; gcongr

theorem polynomialPlan_executes {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S) (plan : List PolynomialStage)
    (hvalid : ∀ op∈plan, op.Valid S) (W : ℕ) (hW : 2≤W)
    (hliteral : ∀ op∈plan, op.LiteralsFit W)
    (hmeta : a.MetadataWidth W) (haWidth : ∀ i, (a.get i).Width W)
    (haValid : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hw : WidthBank S W v)
    (hg : Good S v) (had : PolynomialPlanAdmissible a plan v)
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool)
    (hlen : xs.length≤W) (hylen : ys.length≤W) (s : Store) (hn : addressValue xs=n)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ cost t finalWord, Executes input tape (polynomialPlanCode plan) cost s t ∧
      cost≤polynomialPlanCost n W plan.length ∧
      RationalDataflow.Ready S (polynomialPlanEvaluate a plan v) t ∧ a.Ready t ∧
      BankArray.Word t.val 206 xs ∧ BankArray.Word t.val 201 finalWord ∧
      finalWord.length≤max xs.length ys.length ∧ Good S (polynomialPlanEvaluate a plan v) ∧
      WidthBank S (polynomialPlanWidth n W plan.length) (polynomialPlanEvaluate a plan v) := by
  induction plan generalizing W v ys s with
  | nil =>
    refine ⟨1,s,ys,.skip s,?_,hs,ha,hsaved,hcount,le_max_right _ _,hg,
      hw.mono (polynomialPlanWidth_ge n W 0)⟩
    unfold polynomialPlanCost PolynomialStage.costBound
    simp only [List.length_nil,zero_add,one_mul]
    exact Nat.succ_le_of_lt (by positivity)
  | cons op rest ih =>
    have hB := PolynomialStage.width_ge n W
    obtain ⟨c0,s0,word0,e0,hcost0,ready0,array0,saved0,count0,length0,good0,width0⟩ :=
      op.executes a S h0 h1 h2 (hvalid op (by simp)) W hW (hliteral op (by simp))
        hmeta haWidth haValid v hw hg had.1 input tape xs ys hlen hylen s hn hsaved hcount hs ha
    have wordBound : word0.length≤PolynomialStage.width n W := by
      exact length0.trans ((max_le hlen hylen).trans hB)
    obtain ⟨c1,t,finalWord,e1,hcost1,ready1,array1,saved1,count1,length1,good1,width1⟩ :=
      ih (fun op hop => hvalid op (by simp [hop])) (PolynomialStage.width n W) (hW.trans hB)
        (fun op hop => (hliteral op (by simp [hop])).mono hB) (hmeta.mono hB)
        (fun i => (haWidth i).mono hB) (op.evaluate a v) width0 good0 had.2
        word0 (hlen.trans hB) wordBound s0 saved0 count0 ready0 array0
    have hfinal := polynomialPlanWidth_step n W rest.length
    have hcostmono := PolynomialStage.costBound_mono n hfinal
    have hbase := PolynomialStage.costBound_mono n (polynomialPlanWidth_ge n W (rest.length+1))
    refine ⟨c0+c1,t,finalWord,e0.seq e1,?_,ready1,array1,saved1,count1,?_,good1,width1.mono hfinal⟩
    · have hm := Nat.mul_le_mul_left (rest.length+1) hcostmono
      unfold polynomialPlanCost at hcost1 ⊢
      simp only [List.length_cons]
      nlinarith only [hcost0,hcost1,hm,hbase]
    · exact length1.trans (max_le (le_max_left _ _) length0)

theorem polynomialPlan_computes {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S) (plan : List PolynomialStage)
    (hvalid : ∀ op∈plan, op.Valid S) (W : ℕ) (hW : 2≤W)
    (hliteral : ∀ op∈plan, op.LiteralsFit W)
    (hmeta : a.MetadataWidth W) (haWidth : ∀ i, (a.get i).Width W)
    (haValid : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hw : WidthBank S W v)
    (hg : Good S v) (had : PolynomialPlanAdmissible a plan v)
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool)
    (hlen : xs.length≤W) (hylen : ys.length≤W) (s : Store) (hn : addressValue xs=n)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ t,
      (runPriced ((polynomialPlanCode plan).compile.next input tape)
        (polynomialPlanCost n W plan.length+1) s.val).finished=
          some (t.place (polynomialPlanCode plan).size) ∧
      (runPriced ((polynomialPlanCode plan).compile.next input tape)
        (polynomialPlanCost n W plan.length+1) s.val).instructions≤polynomialPlanCost n W plan.length ∧
      RationalDataflow.Ready S (polynomialPlanEvaluate a plan v) t ∧ a.Ready t ∧
      Good S (polynomialPlanEvaluate a plan v) ∧
      WidthBank S (polynomialPlanWidth n W plan.length) (polynomialPlanEvaluate a plan v) := by
  obtain ⟨cost,t,_,he,hcost,hready,harray,_,_,_,hgood,hwidth⟩ :=
    polynomialPlan_executes a S h0 h1 h2 plan hvalid W hW hliteral hmeta haWidth haValid v hw hg had
      input tape xs ys hlen hylen s hn hsaved hcount hs ha
  obtain ⟨hrun,hsteps⟩ := he.compiled_run (polynomialPlanCost n W plan.length+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hcost,hready,harray,hgood,hwidth⟩

#print axioms polynomialPlan_computes
end Maxwell.Continuum.RationalDataflow.PartArray
