import Maxwell.Composition.SelectedInput
import Maxwell.Realization.BudgetExponents

/-! Literal input-power bounds for the actual source compiler, routed
inverse, and selected physical accuracy. Exponents depend only on the fixed
source promise; the sharper volume estimate is kept separate. -/
noncomputable section
namespace Maxwell.Composition.SelectedLogicalBounds
open Maxwell.Realization Maxwell.Logical
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

theorem constant_bound (m c : ℕ) (hm : 2 ≤ m) : (c : ℚ) ≤ (m : ℚ)^c := by
  have h : c ≤ m^c := (Nat.lt_two_pow_self (n := c)).le.trans (Nat.pow_le_pow_left hm c)
  exact_mod_cast h

theorem mul_bound (m a b : ℕ) {x y : ℚ}
    (hx : x ≤ (m:ℚ)^a) (hy : y ≤ (m:ℚ)^b) (hy0 : 0 ≤ y) :
    x*y ≤ (m:ℚ)^(a+b) := by
  rw [pow_add]
  exact mul_le_mul hx hy hy0 (by positivity)

theorem add_bound (m a b : ℕ) (hm : 2 ≤ m) {x y : ℚ}
    (hx : x ≤ (m:ℚ)^a) (hy : y ≤ (m:ℚ)^b) :
    x+y ≤ (m:ℚ)^(max a b+1) := by
  have hm1 : (1:ℚ) ≤ m := by exact_mod_cast (show 1≤m by omega)
  have ha := hx.trans (pow_le_pow_right₀ hm1 (le_max_left a b))
  have hb := hy.trans (pow_le_pow_right₀ hm1 (le_max_right a b))
  rw [pow_succ]
  have htwo : (2:ℚ) ≤ m := by exact_mod_cast hm
  nlinarith [mul_le_mul_of_nonneg_left htwo (show (0:ℚ)≤(m:ℚ)^max a b by positivity)]

theorem pow_bound (m a k : ℕ) {x : ℚ} (hx0 : 0 ≤ x) (hx : x ≤ (m:ℚ)^a) :
    x^k ≤ (m:ℚ)^(a*k) := by
  rw [pow_mul]
  exact pow_le_pow_left₀ hx0 hx k

def compilerCoefficient (p : Source.Parameters) : ℕ :=
  6*(⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+10)

def compilerExponent (p : Source.Parameters) : ℕ := compilerCoefficient p+2
def sideExponent (p : Source.Parameters) : ℕ := 80+compilerExponent p
def logicalExponent (p : Source.Parameters) : ℕ :=
  9+((1024+sideExponent p)*2)+
    (max (256+(⌈p.conditionExponent⌉₊+1)+compilerExponent p*4) (1024+sideExponent p)+1)
def residualExponent (p : Source.Parameters) : ℕ :=
  4+1+(2*(compilerExponent p+1)+1)+(2048+sideExponent p+1)
def errorExponent (p : Source.Parameters) : ℕ :=
  max 2 (residualExponent p+2+⌈p.accuracyExponent⌉₊)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
local notation "I" => SelectedInput.input p S hm

theorem compiler_size (hunit : IsUnit (Source.realMatrix S)) :
    (sourceCircuit S (I).precision).size ≤ compilerCoefficient p*S.nnz^2 := by
  have hc := sourceCircuit_size S (I).precision (Source.dimension_le_nnz S hunit)
  have hs : S.nnz.size ≤ S.nnz := Nat.size_le.mpr Nat.lt_two_pow_self
  have hbits : (I).precision+1 ≤ (⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+10)*S.nnz := by
    change 7+(⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2)*S.nnz.size+1 ≤ _
    nlinarith
  have h := hc.trans (Nat.mul_le_mul_left (6*S.nnz) hbits)
  convert h using 1
  unfold compilerCoefficient
  ring

theorem compiler_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((sourceCircuit S (I).precision).size : ℚ) ≤ (S.nnz:ℚ)^compilerExponent p := by
  have hc : ((sourceCircuit S (I).precision).size : ℚ) ≤
      compilerCoefficient p*(S.nnz:ℚ)^2 := by exact_mod_cast compiler_size p S hm hunit
  exact hc.trans (mul_bound _ _ _ (constant_bound S.nnz (compilerCoefficient p) hm2) le_rfl (by positivity))

theorem side_size (hm2 : 2 ≤ S.nnz) :
    PhysicalParameters.routingSide S (I).precision ≤ 80*(sourceCircuit S (I).precision).size := by
  have hc := sourceCircuit_size_two_le S hm2 (I).precision
  have hv : 0 < Fintype.card (SourcePositive.Vertex S (I).precision) := by
    change 0 < Fintype.card ((Fin _ ⊕ Fin _) ⊕ _)
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hs := (Routing.portSide_square_bounds _ hv).2
  have hg := SourcePositive.vertex_count_le S (I).precision
  rw [PhysicalParameters.routingSide_eq]
  change SourceRouting.side S (I).precision ≤ _
  change (SourceRouting.side S (I).precision)^2 < _ at hs
  nlinarith

theorem side_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (PhysicalParameters.routingSide S (I).precision : ℚ) ≤ (S.nnz:ℚ)^sideExponent p := by
  have hs : (PhysicalParameters.routingSide S (I).precision : ℚ) ≤
      80*(sourceCircuit S (I).precision).size := by exact_mod_cast side_size p S hm hm2
  exact hs.trans (mul_bound _ _ _ (constant_bound S.nnz 80 hm2)
    (compiler_bound p S hm hm2 hunit) (by positivity))

theorem logical_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (I).logicalBudget ≤ (S.nnz:ℚ)^logicalExponent p := by
  have hc := compiler_bound p S hm hm2 hunit
  have hs := side_bound p S hm hm2 hunit
  have hL : (I).sourceBound = (S.nnz:ℚ)^(⌈p.conditionExponent⌉₊+1) := rfl
  have hL0 : (0:ℚ) ≤ (I).sourceBound := (by norm_num : (0:ℚ) ≤ 1).trans (I).sourceBound_ge_one
  have hl := mul_bound _ _ _ (constant_bound S.nnz 1024 hm2) hs (by positivity)
  have hd := pow_bound _ _ 4 (by positivity) hc
  have ht := mul_bound _ _ _
    (mul_bound _ _ _ (constant_bound S.nnz 256 hm2) (le_of_eq hL) hL0) hd (by positivity)
  have hsum := add_bound _ _ _ hm2 ht hl
  have hsq := pow_bound _ _ 2 (by positivity) hl
  have hprod := mul_bound _ _ _ (mul_bound _ _ _ (constant_bound S.nnz 9 hm2) hsq (by positivity)) hsum
    (by have := (I).sourceBound_ge_one; positivity)
  exact hprod

theorem residual_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (PhysicalAccuracy.residualFactor S (I).precision : ℚ) ≤
      (S.nnz:ℚ)^residualExponent p := by
  have hc := compiler_bound p S hm hm2 hunit
  have hs := side_bound p S hm hm2 hunit
  have hn : (S.n:ℚ) ≤ (S.nnz:ℚ)^1 := by
    simpa only [pow_one] using (show (S.n:ℚ) ≤ S.nnz by exact_mod_cast Source.dimension_le_nnz S hunit)
  have hc1 := add_bound S.nnz (compilerExponent p) 0 hm2 hc (x := (sourceCircuit S (I).precision).size)
    (y := 1) (by simp)
  simp only [max_zero] at hc1
  have hc2 := pow_bound _ _ 2 (by positivity) hc1
  have hc3 := add_bound S.nnz _ 0 hm2 hc2 (y := 1) (by simp)
  simp only [max_zero] at hc3
  have ht0 := mul_bound _ _ _ (constant_bound S.nnz 2048 hm2) hs (by positivity)
  have ht := add_bound S.nnz _ 0 hm2 ht0 (y := 1) (by simp)
  simp only [max_zero] at ht
  have hr := mul_bound _ _ _
    (mul_bound _ _ _ (mul_bound _ _ _ (constant_bound S.nnz 4 hm2) hn (by positivity))
      hc3 (by positivity)) ht (by positivity)
  convert hr using 1
  · simp only [PhysicalAccuracy.residualFactor, routedResidualFactor, positiveResidualFactor,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    ring
  · apply congrArg (fun e : ℕ => (S.nnz:ℚ)^e)
    dsimp only [residualExponent]
    omega

theorem denominator_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (PhysicalAccuracy.denominator S (I).precision : ℚ) ≤
      (S.nnz:ℚ)^(residualExponent p+2) := by
  have hm1 : (1:ℚ) ≤ S.nnz := by exact_mod_cast hm
  have hr : max 1 (PhysicalAccuracy.residualFactor S (I).precision : ℚ) ≤
      (S.nnz:ℚ)^residualExponent p :=
    max_le (one_le_pow₀ hm1) (residual_bound p S hm hm2 hunit)
  have hm2' : max 1 ((S.nnz:ℚ)^2) ≤ (S.nnz:ℚ)^2 := max_le (one_le_pow₀ hm1) le_rfl
  have h := mul_bound _ _ _ hr hm2' (by positivity)
  simpa only [PhysicalAccuracy.denominator, Nat.cast_mul, Nat.cast_max,
    Nat.cast_one, Nat.cast_pow] using h

theorem error_inverse_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (I).epsilon⁻¹ ≤ (S.nnz:ℚ)^errorExponent p := by
  have hm1 : (1:ℚ) ≤ S.nnz := by exact_mod_cast hm
  have ha : (I).accuracy⁻¹ = (S.nnz:ℚ)^⌈p.accuracyExponent⌉₊ := by
    simp [SelectedInput.input, logicalAccuracy]
  have hd := denominator_bound p S hm hm2 hunit
  change (min (1/2) ((I).accuracy/(PhysicalAccuracy.denominator S (I).precision : ℚ)))⁻¹ ≤ _
  by_cases h : (1/2:ℚ) ≤ (I).accuracy/(PhysicalAccuracy.denominator S (I).precision : ℚ)
  · rw [min_eq_left h]
    norm_num only [inv_div, inv_one, div_one]
    exact (constant_bound S.nnz 2 hm2).trans (pow_le_pow_right₀ hm1 (le_max_left _ _))
  · rw [min_eq_right (le_of_not_ge h), inv_div, div_eq_mul_inv, ha]
    exact (mul_bound _ _ _ hd le_rfl (by positivity)).trans
      (pow_le_pow_right₀ hm1 (le_max_right _ _))

end Maxwell.Composition.SelectedLogicalBounds
