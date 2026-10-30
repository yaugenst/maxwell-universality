import Maxwell.Continuum.DefinitenessExpressionTrace

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
  have he : 1≤extent A := extent_pos A
  have hwB : W≤extent A*(W+1) := by nlinarith
  have hvalid := control_valid A out s (s+extent A) (by omega) hA (by rfl)
  have htrace := control_widthTrace A out s hA (Finset.range (s+extent A))
    (extent A*(W+1)) W (by rfl) v (hw.mono hwB)
    (fun i hi => hw i (Finset.mem_range.mpr (by omega)))
  obtain ⟨cost,t,hexe,hcost,hready,_hframe⟩ := (control A out s).executes
    (Finset.range (s+extent A)) hvalid v (extent A*(W+1)) htrace hg
    (control_admissible A out s hA v hsafe) input tape st hst
  have hc := hcost.trans (quadratic_cost A out s W)
  obtain ⟨hrun,hcharged⟩ := hexe.compiled_run (costConstant A out s*(W+1)^2+1) (by omega)
  exact ⟨cost,t,(control A out s).evaluate v,hrun,hcharged,hc,hready,control_result A out s hA v⟩

#print axioms control_computes

end Maxwell.Continuum.Calibration.ExpressionDefiniteness
