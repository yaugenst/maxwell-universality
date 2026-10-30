import Maxwell.Continuum.RationalDataflowPolynomialMeaning
import Maxwell.Continuum.CutoffAntiderivativeTable

/-! A single fixed cutoff query schedule, independent of requested precision.
Its runtime inputs are the coordinate words and finite antiderivative table. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

def querySlots : Finset ℕ := Finset.range 32

def denominatorSetup : List PolynomialStage :=
  [.arithmetic (.literal 6 0),.arithmetic (.literal 3 (-1/2)),.query 3 4,
   .arithmetic (.literal 3 (1/2)),.query 3 5,.arithmetic (.binary .sub 8 5 4)]

def psiPlan (source target : ℕ) : List PolynomialStage :=
  [.arithmetic (.literal 7 (3/2)),.arithmetic (.binary .sub 0 source 7),.clamp,
   .arithmetic (.binary .add 3 0 6),.query 3 4,
   .arithmetic (.binary .add 0 source 7),.clamp,
   .arithmetic (.binary .add 3 0 6),.query 3 5,
   .arithmetic (.binary .sub target 5 4),.arithmetic (.binary .mul target target 9)]

def cutoffQueryPlan : List PolynomialStage := denominatorSetup++
  [.arithmetic (.inverse 9 8)]++psiPlan 10 13++psiPlan 11 14++psiPlan 12 15++
  [.arithmetic (.binary .mul 16 13 14),.arithmetic (.binary .mul 16 16 15)]

theorem cutoffQueryPlan_length : cutoffQueryPlan.length=42 := rfl

theorem cutoffQueryPlan_valid : ∀ op∈cutoffQueryPlan, op.Valid querySlots := by
  simp [cutoffQueryPlan,denominatorSetup,psiPlan,PolynomialStage.Valid,Instruction.Valid,querySlots]

theorem cutoffQueryPlan_literals (W : ℕ) (hW : 3≤W) :
    ∀ op∈cutoffQueryPlan, op.LiteralsFit W := by
  have hsmall : ∀ op∈cutoffQueryPlan, op.LiteralsFit 3 := by
    have hzero : (Parts.literal 0).Width 3 := by unfold Parts.Width Parts.literal; decide
    have hhalf : (Parts.literal (2⁻¹)).Width 3 := by
      simpa only [one_div] using (Parts.literal_width cutoff_half_width).mono (by decide : 2≤3)
    have hneg : (Parts.literal (-1/2)).Width 3 :=
      (Parts.literal_width (by simpa only [neg_div] using cutoff_half_width.neg)).mono (by decide)
    have hthree : (Parts.literal (3/2)).Width 3 := by
      apply Parts.literal_width
      have h := RationalWords.width_fraction (z := 3) (d := 2) (B := 3)
        (by decide) (by decide) (by decide)
      simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h
    simp [cutoffQueryPlan,denominatorSetup,psiPlan,PolynomialStage.LiteralsFit,
      Instruction.LiteralFits,hzero,hhalf,hneg,hthree]
  exact fun op ho => (hsmall op ho).mono hW

theorem denominatorSetup_admissible {n : ℕ} (a : Table n) (v : ℕ→Parts) :
    PolynomialPlanAdmissible a denominatorSetup v := by
  simp only [denominatorSetup,PolynomialPlanAdmissible,PolynomialStage.Admissible,
    Instruction.Admissible,and_self]

theorem psiPlan_admissible {n : ℕ} (a : Table n) (source target : ℕ) (v : ℕ→Parts) :
    PolynomialPlanAdmissible a (psiPlan source target) v := by
  simp only [psiPlan,PolynomialPlanAdmissible,PolynomialStage.Admissible,
    Instruction.Admissible,and_self]

theorem clampRational_zero (v : ℕ→ℚ) :
    clampControl.rationalEvaluate v 0=cutoffClampRat (v 0) := by
  let raw : ℕ→Parts := fun i => Parts.literal (v i)
  have hv : Good querySlots raw := fun _ _ => Parts.literal_valid _
  have he := clampControl.evaluate_value querySlots
    (clampControl_valid querySlots (by decide) (by decide) (by decide)) raw hv
    (clampControl_admissible raw)
  have hraw : valueBank raw=v := by funext i; exact Parts.literal_value _
  rw [hraw] at he
  rw [← congrFun he 0]
  change (clampControl.evaluate raw 0).value=_
  rw [clampControl_value raw (Parts.literal_valid _),clamp_value,Parts.literal_value]

theorem clampRational_keep (v : ℕ→ℚ) (i : ℕ) (h0 : i≠0) (h1 : i≠1) (h2 : i≠2) :
    clampControl.rationalEvaluate v i=v i := by
  let raw : ℕ→Parts := fun i => Parts.literal (v i)
  have hv : Good querySlots raw := fun _ _ => Parts.literal_valid _
  have he := clampControl.evaluate_value querySlots
    (clampControl_valid querySlots (by decide) (by decide) (by decide)) raw hv
    (clampControl_admissible raw)
  have hraw : valueBank raw=v := by funext i; exact Parts.literal_value _
  rw [hraw] at he
  rw [← congrFun he i]
  change (clampControl.evaluate raw i).value=_
  rw [clampControl_keep raw i h0 h1 h2,Parts.literal_value]

theorem queryRational_target {n : ℕ} (a : Table n) (point target : ℕ) (v : ℕ→ℚ) :
    antiderivativeRationalState a point target v target=primitiveValue a (v point) := by
  exact Function.update_self _ _ _

theorem queryRational_keep {n : ℕ} (a : Table n) (point target : ℕ) (v : ℕ→ℚ) (i : ℕ)
    (h0 : i≠0) (h1 : i≠1) (h2 : i≠2) (ht : i≠target) :
    antiderivativeRationalState a point target v i=v i := by
  simp only [antiderivativeRationalState,Function.update_of_ne h0,Function.update_of_ne h1,
    Function.update_of_ne h2,Function.update_of_ne ht]

theorem denominatorSetup_values {n : ℕ} (a : Table n) (v : ℕ→ℚ) :
    (polynomialPlanRationalEvaluate a denominatorSetup v) 8=
      primitiveValue a (1/2)-primitiveValue a (-1/2) ∧
    (polynomialPlanRationalEvaluate a denominatorSetup v) 6=0 ∧
    (∀ i, 10 ≤ i → polynomialPlanRationalEvaluate a denominatorSetup v i=v i) := by
  constructor
  · simp [denominatorSetup,polynomialPlanRationalEvaluate,PolynomialStage.rationalEvaluate,
      Instruction.rationalUpdate,queryRational_target,queryRational_keep]
  constructor
  · simp [denominatorSetup,polynomialPlanRationalEvaluate,PolynomialStage.rationalEvaluate,
      Instruction.rationalUpdate,queryRational_target,queryRational_keep]
  · intro i hi
    simp (disch := omega) only [denominatorSetup,polynomialPlanRationalEvaluate,
      PolynomialStage.rationalEvaluate,Instruction.rationalUpdate,queryRational_keep,
      Function.update_of_ne]

theorem psiPlan_value {n : ℕ} (a : Table n) (source target : ℕ)
    (hs : 10≤source) (ht : 13≤target) (v : ℕ→ℚ) (hz : v 6=0) :
    polynomialPlanRationalEvaluate a (psiPlan source target) v target=
      (primitiveValue a (cutoffClampRat (v source+3/2))-
        primitiveValue a (cutoffClampRat (v source-3/2)))*v 9 := by
  simp (disch := omega) only [psiPlan,polynomialPlanRationalEvaluate,
    PolynomialStage.rationalEvaluate,Instruction.rationalUpdate,queryRational_target,queryRational_keep,
    Function.update_self,Function.update_of_ne,clampRational_zero,clampRational_keep,hz,add_zero]

theorem psiPlan_keep {n : ℕ} (a : Table n) (source target : ℕ) (v : ℕ→ℚ)
    (i : ℕ) (hi : 6 ≤ i) (hi7 : i≠7) (hit : i≠target) :
    polynomialPlanRationalEvaluate a (psiPlan source target) v i=v i := by
  simp (disch := omega) only [psiPlan,polynomialPlanRationalEvaluate,
    PolynomialStage.rationalEvaluate,Instruction.rationalUpdate,queryRational_keep,
    Function.update_of_ne,clampRational_keep]

theorem table_primitive_difference (N : ℕ) (a : Table (Profile.profileDegree N))
    (hcoeff : ∀ i, (a.get i).value=(antiderivativeCoefficient N i).value) (x y : ℚ) :
    primitiveValue a y-primitiveValue a x=cutoffIntegralApprox N x y := by
  simp only [primitiveValue,polynomialValue,hcoeff]
  exact antiderivative_difference N x y

#print axioms cutoffQueryPlan_valid
#print axioms psiPlan_value
end Maxwell.Continuum.Calibration.RawCutoff
