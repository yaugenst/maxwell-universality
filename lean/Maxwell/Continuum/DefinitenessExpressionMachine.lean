import Maxwell.Continuum.DefinitenessExpressionTrace
import Maxwell.Continuum.RationalDataflowControlTraceResult

/-! The symbolic circuit is a Boolean-machine program. With a fixed symbolic
matrix its charged running time is quadratic in the runtime operand width. -/

namespace Maxwell.Continuum.Calibration.ExpressionDefiniteness

open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured

def costConstant {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression) (out s : ℕ) : ℕ :=
  (control A out s).steps*2^100*(extent A+3)^2+1

theorem quadratic_cost {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression) (out s W : ℕ) :
    (control A out s).steps*operationCost (extent A*(W+1))+1≤costConstant A out s*(W+1)^2 := by
  have hw : extent A*(W+1)+3≤(extent A+3)*(W+1) := by nlinarith
  calc
    _ ≤ (control A out s).steps*(2^100*((extent A+3)*(W+1))^2)+1 := by
      unfold operationCost
      gcongr
    _ = (control A out s).steps*2^100*(extent A+3)^2*(W+1)^2+1 := by ring
    _ ≤ costConstant A out s*(W+1)^2 := by
      unfold costConstant
      have h1 : 1≤(W+1)^2 := by nlinarith
      nlinarith only [h1]

theorem control_executes_in {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (out s M : ℕ) (ho : out<s) (fit : s+extent A≤M) (hA : Below A s) (v : ℕ → Parts) (W : ℕ)
    (hw : WidthBank (Finset.range M) W v)
    (hg : Good (Finset.range M) v) (hsafe : Safe A v)
    (input : List Bool) (tape : ℕ → Bool) (st : Store)
    (hst : Ready (Finset.range M) v st) :
    let output:=(control A out s).evaluate v
    ∃cost t,Executes input tape (control A out s).code cost st t ∧
      cost≤costConstant A out s*(W+1)^2 ∧ Ready (Finset.range M) output t ∧
      Good (Finset.range M) output ∧
      WidthBank (Finset.range M) (extent A*(W+1)) output ∧
      output out=Parts.literal (if RawDefiniteness.positive (evaluate A v) then 1 else 0) ∧
      BinaryPrecision.Frame (workspace (Finset.range M)) st.val t.val := by
  dsimp only
  have he : 1≤extent A := extent_pos A
  have hwB : W≤extent A*(W+1) := by nlinarith
  have hvalid := control_valid A out s M (by omega) hA fit
  have htrace := control_widthTrace A out s hA (Finset.range M)
    (extent A*(W+1)) W (by rfl) v (hw.mono hwB)
    (fun i hi => hw i (Finset.mem_range.mpr (by omega)))
  obtain ⟨cost,t,hexe,hcost,hready,hframe⟩ := (control A out s).executes
    (Finset.range M) hvalid v (extent A*(W+1)) htrace hg
    (control_admissible A out s hA v hsafe) input tape st hst
  have hc := hcost.trans (quadratic_cost A out s W)
  exact ⟨cost,t,hexe,hc,hready,
    (control A out s).evaluate_good _ hvalid v hg (control_admissible A out s hA v hsafe),
    htrace.result,control_result A out s hA v,hframe⟩

theorem control_executes {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (out s : ℕ) (ho : out<s) (hA : Below A s) (v : ℕ → Parts) (W : ℕ)
    (hw : WidthBank (Finset.range (s+extent A)) W v)
    (hg : Good (Finset.range (s+extent A)) v) (hsafe : Safe A v)
    (input : List Bool) (tape : ℕ → Bool) (st : Store)
    (hst : Ready (Finset.range (s+extent A)) v st) :
    let output:=(control A out s).evaluate v
    ∃cost t,Executes input tape (control A out s).code cost st t ∧
      cost≤costConstant A out s*(W+1)^2 ∧ Ready (Finset.range (s+extent A)) output t ∧
      Good (Finset.range (s+extent A)) output ∧
      WidthBank (Finset.range (s+extent A)) (extent A*(W+1)) output ∧
      output out=Parts.literal (if RawDefiniteness.positive (evaluate A v) then 1 else 0) ∧
      BinaryPrecision.Frame (workspace (Finset.range (s+extent A))) st.val t.val := by
  exact control_executes_in A out s (s+extent A) ho le_rfl hA v W hw hg hsafe input tape st hst

theorem control_computes {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (out s : ℕ) (ho : out<s) (hA : Below A s) (v : ℕ → Parts) (W : ℕ)
    (hw : WidthBank (Finset.range (s+extent A)) W v)
    (hg : Good (Finset.range (s+extent A)) v) (hsafe : Safe A v)
    (input : List Bool) (tape : ℕ → Bool) (st : Store)
    (hst : Ready (Finset.range (s+extent A)) v st) :
    ∃ cost t output,
      (runPriced ((control A out s).code.compile.next input tape)
        (costConstant A out s*(W+1)^2+1) st.val).finished=some (t.place (control A out s).code.size) ∧
      (runPriced ((control A out s).code.compile.next input tape)
        (costConstant A out s*(W+1)^2+1) st.val).instructions=cost ∧
      cost≤costConstant A out s*(W+1)^2 ∧ Ready (Finset.range (s+extent A)) output t ∧
      output out=Parts.literal (if RawDefiniteness.positive (evaluate A v) then 1 else 0) := by
  obtain ⟨cost,t,execution,bound,ready,_,_,result,_⟩:=
    control_executes A out s ho hA v W hw hg hsafe input tape st hst
  obtain ⟨run,charged⟩:=execution.compiled_run (costConstant A out s*(W+1)^2+1) (by omega)
  exact ⟨cost,t,(control A out s).evaluate v,run,charged,bound,ready,result⟩

#print axioms control_computes

end Maxwell.Continuum.Calibration.ExpressionDefiniteness
