import Maxwell.Continuum.CutoffQueryCertified

/-! Cutoff queries consume the actual unreduced coefficient table produced
by finite arithmetic. Only coefficient values, validity and raw word widths
matter; no canonical-rational equality or precomputed-table oracle is used. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
attribute [local irreducible] polynomialPlanEvaluate polynomialPlanCode cutoffQueryPlan chiCenter Well.chi

def storedCutoffQueryCode : Code := polynomialPlanCode cutoffQueryPlan

theorem storedCutoffQuery_executes (N : ℕ) (a : Table (Profile.profileDegree N))
    (hvalue : ∀i,(a.get i).value=(antiderivativeCoefficient N i).value)
    (W : ℕ) (hW : 3≤W) (hwidth : ∀i,(a.get i).Width W) (hvalid : ∀i,(a.get i).Valid)
    (hmeta : a.MetadataWidth W) (v : ℕ→Parts) (hw : WidthBank querySlots W v) (hg : Good querySlots v)
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool) (hlen : xs.length≤W) (hold : ys.length≤W)
    (s : Store) (hn : addressValue xs=Profile.profileDegree N)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys)
    (hs : RationalDataflow.Ready querySlots v s) (ha : a.Ready s) :
    ∃ cost t output,Executes input tape storedCutoffQueryCode cost s t ∧
      cost≤polynomialPlanCost (Profile.profileDegree N) W 42 ∧
      RationalDataflow.Ready querySlots output t ∧ Good querySlots output ∧ a.Ready t ∧
      WidthBank querySlots (polynomialPlanWidth (Profile.profileDegree N) W 42) output ∧
      (output 16).value=chiCenter (fun i : Fin 3 => (v (10+i.val)).value) N := by
  obtain ⟨cost,t,_,ex,hcost,rt,at',_,_,_,gt,wt⟩ := polynomialPlan_executes a querySlots
    (by decide) (by decide) (by decide) cutoffQueryPlan cutoffQueryPlan_valid W (by omega)
    (cutoffQueryPlan_literals W hW) hmeta hwidth hvalid v hw hg
    (cutoffQueryPlan_admissible N a hvalue hvalid v hg) input tape xs ys hlen hold s hn
    hsaved hcount hs ha
  exact ⟨cost,t,polynomialPlanEvaluate a cutoffQueryPlan v,ex,
    by simpa only [cutoffQueryPlan_length] using hcost,rt,gt,at',
    by simpa only [cutoffQueryPlan_length] using wt,cutoffQueryPlan_value N a hvalue hvalid v hg⟩

theorem storedCutoffQuery_computes_enclosure (N : ℕ) (a : Table (Profile.profileDegree N))
    (hvalue : ∀i,(a.get i).value=(antiderivativeCoefficient N i).value)
    (W : ℕ) (hW : 3≤W) (hwidth : ∀i,(a.get i).Width W) (hvalid : ∀i,(a.get i).Valid)
    (hmeta : a.MetadataWidth W) (v : ℕ→Parts) (hw : WidthBank querySlots W v) (hg : Good querySlots v)
    (q₀ : ℝ) (x : Space)
    (hx : ∀i : Fin 3,|x i/q₀-((v (10+i.val)).value:ℝ)|≤(1/2:ℝ)^(N+12))
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool) (hlen : xs.length≤W) (hold : ys.length≤W)
    (s : Store) (hn : addressValue xs=Profile.profileDegree N)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys)
    (hs : RationalDataflow.Ready querySlots v s) (ha : a.Ready s) :
    ∃ (t : Store) (output : ℕ→Parts),
      (runPriced (storedCutoffQueryCode.compile.next input tape)
        (polynomialPlanCost (Profile.profileDegree N) W 42+1) s.val).finished=
          some (t.place storedCutoffQueryCode.size) ∧
      (runPriced (storedCutoffQueryCode.compile.next input tape)
        (polynomialPlanCost (Profile.profileDegree N) W 42+1) s.val).instructions≤
          polynomialPlanCost (Profile.profileDegree N) W 42 ∧
      RationalDataflow.Ready querySlots output t ∧ Good querySlots output ∧ a.Ready t ∧
      WidthBank querySlots (polynomialPlanWidth (Profile.profileDegree N) W 42) output ∧
      |Well.chi q₀ x-((output 16).value:ℝ)|≤(1/2:ℝ)^N := by
  obtain ⟨cost,t,output,ex,hcost,rt,gt,at',wt,hout⟩ := storedCutoffQuery_executes N a hvalue W hW
    hwidth hvalid hmeta v hw hg input tape xs ys hlen hold s hn hsaved hcount hs ha
  obtain ⟨hrun,hsteps⟩ := ex.compiled_run (polynomialPlanCost (Profile.profileDegree N) W 42+1) (by omega)
  refine ⟨t,output,hrun,hsteps ▸ hcost,rt,gt,at',wt,?_⟩
  rw [hout]
  have he := chiApprox_contains (fun i : Fin 3 => (v (10+i.val)).value) N q₀ x hx
  change |Well.chi q₀ x-(chiCenter (fun i : Fin 3 => (v (10+i.val)).value) N:ℝ)|≤
    (((1/2:ℚ)^N:ℚ):ℝ) at he
  simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using he

#print axioms storedCutoffQuery_computes_enclosure
end Maxwell.Continuum.Calibration.RawCutoff
