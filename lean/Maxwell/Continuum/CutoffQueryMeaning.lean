import Maxwell.Continuum.CutoffQueryPlan

/-! The fixed query schedule returns the literal certified cutoff approximation. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768
attribute [local irreducible] psiCenter chiCenter cutoffDenominatorApprox cutoffIntegralApprox

def queryTail : List PolynomialStage := psiPlan 10 13++psiPlan 11 14++psiPlan 12 15++
  [.arithmetic (.binary .mul 16 13 14),.arithmetic (.binary .mul 16 16 15)]

theorem cutoffQueryPlan_eq : cutoffQueryPlan=
    denominatorSetup++(.arithmetic (.inverse 9 8)::queryTail) := by
  simp only [cutoffQueryPlan,queryTail,List.append_assoc,List.cons_append,List.nil_append]

theorem queryTail_admissible {n : ℕ} (a : Table n) (v : ℕ→Parts) :
    PolynomialPlanAdmissible a queryTail v := by
  simp only [queryTail,polynomialPlanAdmissible_append,psiPlan_admissible,
    PolynomialPlanAdmissible,PolynomialStage.Admissible,Instruction.Admissible,and_self]

theorem psiPlan_actual (N : ℕ) (a : Table (Profile.profileDegree N))
    (hcoeff : ∀ i, (a.get i).value=(antiderivativeCoefficient N i).value)
    (source target : ℕ) (hs : 10≤source) (ht : 13≤target) (v : ℕ→ℚ)
    (hz : v 6=0) (hd : v 9=(cutoffDenominatorApprox N)⁻¹) :
    polynomialPlanRationalEvaluate a (psiPlan source target) v target=psiCenter (v source) N := by
  rw [psiPlan_value a source target hs ht v hz,
    table_primitive_difference N a hcoeff,hd]
  unfold psiCenter psiNumeratorApprox
  rfl

theorem cutoffQueryPlan_admissible (N : ℕ) (a : Table (Profile.profileDegree N))
    (hcoeff : ∀ i, (a.get i).value=(antiderivativeCoefficient N i).value)
    (ha : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hv : Good querySlots v) :
    PolynomialPlanAdmissible a cutoffQueryPlan v := by
  rw [cutoffQueryPlan_eq,polynomialPlanAdmissible_append]
  refine ⟨denominatorSetup_admissible a v,?_,queryTail_admissible a _⟩
  change (polynomialPlanEvaluate a denominatorSetup v 8).value≠0
  have he := congrFun (polynomialPlan_evaluate_value a querySlots
    (by decide) (by decide) (by decide) denominatorSetup
    (by simp [denominatorSetup,PolynomialStage.Valid,Instruction.Valid,querySlots]) ha v hv
    (denominatorSetup_admissible a v)) 8
  change (polynomialPlanEvaluate a denominatorSetup v 8).value=_ at he
  rw [(denominatorSetup_values a (valueBank v)).1,table_primitive_difference N a hcoeff] at he
  rw [he]
  have hp := cutoffDenominatorApprox_lower N
  change cutoffIntegralApprox N (-1/2) (1/2)≠0
  unfold cutoffDenominatorApprox at hp
  linarith

theorem queryTail_value (N : ℕ) (a : Table (Profile.profileDegree N))
    (hcoeff : ∀ i, (a.get i).value=(antiderivativeCoefficient N i).value)
    (v : ℕ→ℚ) (hz : v 6=0) (hd : v 9=(cutoffDenominatorApprox N)⁻¹) :
    polynomialPlanRationalEvaluate a queryTail v 16=
      psiCenter (v 10) N*psiCenter (v 11) N*psiCenter (v 12) N := by
  let v1 := polynomialPlanRationalEvaluate a (psiPlan 10 13) v
  let v2 := polynomialPlanRationalEvaluate a (psiPlan 11 14) v1
  let v3 := polynomialPlanRationalEvaluate a (psiPlan 12 15) v2
  have z1 : v1 6=0 := (psiPlan_keep a 10 13 v 6 (by decide) (by decide) (by decide)).trans hz
  have d1 : v1 9=(cutoffDenominatorApprox N)⁻¹ :=
    (psiPlan_keep a 10 13 v 9 (by decide) (by decide) (by decide)).trans hd
  have z2 : v2 6=0 := (psiPlan_keep a 11 14 v1 6 (by decide) (by decide) (by decide)).trans z1
  have d2 : v2 9=(cutoffDenominatorApprox N)⁻¹ :=
    (psiPlan_keep a 11 14 v1 9 (by decide) (by decide) (by decide)).trans d1
  have p1 : v1 13=psiCenter (v 10) N :=
    psiPlan_actual N a hcoeff 10 13 (by decide) (by decide) v hz hd
  have p2 : v2 14=psiCenter (v 11) N := by
    exact (psiPlan_actual N a hcoeff 11 14 (by decide) (by decide) v1 z1 d1).trans
      (congrArg (fun q => psiCenter q N)
        (psiPlan_keep a 10 13 v 11 (by decide) (by decide) (by decide)))
  have p3 : v3 15=psiCenter (v 12) N := by
    exact (psiPlan_actual N a hcoeff 12 15 (by decide) (by decide) v2 z2 d2).trans
      (congrArg (fun q => psiCenter q N)
        ((psiPlan_keep a 11 14 v1 12 (by decide) (by decide) (by decide)).trans
          (psiPlan_keep a 10 13 v 12 (by decide) (by decide) (by decide))))
  have p1' : v3 13=psiCenter (v 10) N :=
    (psiPlan_keep a 12 15 v2 13 (by decide) (by decide) (by decide)).trans
      ((psiPlan_keep a 11 14 v1 13 (by decide) (by decide) (by decide)).trans p1)
  have p2' : v3 14=psiCenter (v 11) N :=
    (psiPlan_keep a 12 15 v2 14 (by decide) (by decide) (by decide)).trans p2
  simp only [queryTail,polynomialPlanRationalEvaluate_append]
  change polynomialPlanRationalEvaluate a
    [.arithmetic (.binary .mul 16 13 14),.arithmetic (.binary .mul 16 16 15)] v3 16=_
  simp only [polynomialPlanRationalEvaluate,PolynomialStage.rationalEvaluate,
    Instruction.rationalUpdate,Function.update_self,Function.update_of_ne (by decide : (15:ℕ)≠16),
    p1',p2',p3]

theorem rationalEvaluate_cons {n : ℕ} (a : Table n) (op : PolynomialStage)
    (rest : List PolynomialStage) (v : ℕ→ℚ) :
    polynomialPlanRationalEvaluate a (op::rest) v=
      polynomialPlanRationalEvaluate a rest (op.rationalEvaluate a v) := rfl

attribute [local irreducible] polynomialPlanRationalEvaluate queryTail psiPlan

theorem cutoffQueryPlan_rational_value (N : ℕ) (a : Table (Profile.profileDegree N))
    (hcoeff : ∀ i, (a.get i).value=(antiderivativeCoefficient N i).value) (v : ℕ→ℚ) :
    polynomialPlanRationalEvaluate a cutoffQueryPlan v 16=
      chiCenter (fun i : Fin 3 => v (10+i.val)) N := by
  let prepared := polynomialPlanRationalEvaluate a denominatorSetup v
  have den : prepared 8=cutoffDenominatorApprox N := by
    change polynomialPlanRationalEvaluate a denominatorSetup v 8=_
    rw [(denominatorSetup_values a v).1,table_primitive_difference N a hcoeff]
    unfold cutoffDenominatorApprox
    rfl
  let normalized := Function.update prepared 9 (prepared 8)⁻¹
  have hz : normalized 6=0 := by
    dsimp only [normalized]
    rw [Function.update_of_ne (by decide : (6:ℕ)≠9)]
    exact (denominatorSetup_values a v).2.1
  have hd : normalized 9=(cutoffDenominatorApprox N)⁻¹ := by
    dsimp only [normalized]
    rw [Function.update_self,den]
  have keep (i : ℕ) (hi : 10 ≤ i) : normalized i=v i := by
    dsimp only [normalized]
    rw [Function.update_of_ne (by omega)]
    exact (denominatorSetup_values a v).2.2 i hi
  rw [cutoffQueryPlan_eq,polynomialPlanRationalEvaluate_append]
  rw [rationalEvaluate_cons]
  change polynomialPlanRationalEvaluate a queryTail normalized 16=_
  rw [queryTail_value N a hcoeff normalized hz hd,
    keep 10 (by decide),keep 11 (by decide),keep 12 (by decide)]
  simp only [chiCenter,Fin.prod_univ_three]
  rfl

theorem cutoffQueryPlan_value (N : ℕ) (a : Table (Profile.profileDegree N))
    (hcoeff : ∀ i, (a.get i).value=(antiderivativeCoefficient N i).value)
    (ha : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hv : Good querySlots v) :
    (polynomialPlanEvaluate a cutoffQueryPlan v 16).value=
      chiCenter (fun i : Fin 3 => (v (10+i.val)).value) N := by
  have he := congrFun (polynomialPlan_evaluate_value a querySlots (by decide) (by decide) (by decide)
    cutoffQueryPlan cutoffQueryPlan_valid ha v hv (cutoffQueryPlan_admissible N a hcoeff ha v hv)) 16
  exact he.trans (cutoffQueryPlan_rational_value N a hcoeff (valueBank v))

#print axioms cutoffQueryPlan_admissible
#print axioms cutoffQueryPlan_value
end Maxwell.Continuum.Calibration.RawCutoff
