import Maxwell.Continuum.ParameterInputBudget
import Maxwell.Continuum.ParameterSourceSites
import Maxwell.Composition.SelectedLogicalBounds

/-! The binary analysis budget is discharged from the actual sparse-source
compiler, routed graph, logical inverse, and residual tolerance. No discrete
Maxwell certificate is an assumption of these results. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open Maxwell.Composition Maxwell.Logical Maxwell.Realization

attribute [local irreducible] Composition.SelectedInput.input
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

 def sourceInput (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) : Input where
  m := S.nnz
  J := Fintype.card (SourceDecoration.Vertex S (SelectedInput.input p S hm).precision)
  span := fun _ => 2^54*129*PhysicalParameters.routingSide S (SelectedInput.input p S hm).precision
  K := (SelectedInput.input p S hm).logicalBudget
  epsilon := (SelectedInput.input p S hm).epsilon/16
  m_pos := hm
  K_pos := zero_lt_one.trans_le (SelectedInstance.Input.logicalBudget_ge_one _)
  epsilon_pos := div_pos (SelectedInstance.Input.epsilon_pos _) (by norm_num)

/-- A fixed exponent depending only on the source promise. -/
 def sourceBudgetExponent (p : Source.Parameters) : ℕ :=
  81000+3*SelectedLogicalBounds.sideExponent p+SelectedLogicalBounds.logicalExponent p+
    SelectedLogicalBounds.errorExponent p

 theorem sourceInput_binary (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (sourceInput p S hm).BinaryBudget (sourceBudgetExponent p) (inputLog S.nnz) := by
  let I := SelectedInput.input p S hm
  let P := sourceBudgetExponent p
  let ℓ := inputLog S.nnz
  have hm1 : (1 : ℚ) ≤ S.nnz := by exact_mod_cast (show 1 ≤ S.nnz by omega)
  have hmQ : (S.nnz : ℚ) ≤ (2 : ℚ)^ℓ := by exact_mod_cast input_le_binary S.nnz
  have hpow (a : ℕ) : (S.nnz : ℚ)^a ≤ (2 : ℚ)^(a*ℓ) := by
    have h := binary_pow (Nat.cast_nonneg S.nnz) hmQ a
    simpa only [Nat.mul_comm ℓ a] using h
  have hpromote {x : ℚ} {a : ℕ} (hx : x ≤ (S.nnz : ℚ)^a) (ha : a ≤ P) :
      x ≤ (2 : ℚ)^(P*ℓ) :=
    (hx.trans (hpow a)).trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right ℓ ha))
  have hside := SelectedLogicalBounds.side_bound p S hm hm2 hunit
  change (PhysicalParameters.routingSide S I.precision : ℚ) ≤
    (S.nnz : ℚ)^SelectedLogicalBounds.sideExponent p at hside
  have hV : (Fintype.card (SourceRouting.Vertex S I.precision) : ℚ) ≤
      (S.nnz : ℚ)^(80625+3*SelectedLogicalBounds.sideExponent p) := by
    have hnat := (SourceRouting.vertex_card_le_box S I.precision).trans
      (SourceRouting.box_volume_le_cube S I.precision)
    rw [← PhysicalParameters.routingSide_eq] at hnat
    have hraw : (Fintype.card (SourceRouting.Vertex S I.precision) : ℚ) ≤
        80625*(PhysicalParameters.routingSide S I.precision : ℚ)^3 := by exact_mod_cast hnat
    have hprod := SelectedLogicalBounds.mul_bound _ _ _
      (SelectedLogicalBounds.constant_bound S.nnz 80625 hm2)
      (SelectedLogicalBounds.pow_bound _ _ 3 (Nat.cast_nonneg _) hside) (by positivity)
    apply hraw.trans
    simpa only [Nat.cast_ofNat, Nat.mul_comm (SelectedLogicalBounds.sideExponent p) 3] using hprod
  have hJ : (Fintype.card (SourceDecoration.Vertex S I.precision) : ℚ) ≤
      (S.nnz : ℚ)^(80627+3*SelectedLogicalBounds.sideExponent p) := by
    have hraw : (Fintype.card (SourceDecoration.Vertex S I.precision) : ℚ) ≤
        4*(Fintype.card (SourceRouting.Vertex S I.precision) : ℚ) := by
      exact_mod_cast sourceWell_card S I.precision
    have h4 : (4 : ℚ) ≤ (S.nnz : ℚ)^2 := by
      exact (show (4 : ℚ) = 2^2 by norm_num).le.trans
        (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm2) 2)
    have hprod := SelectedLogicalBounds.mul_bound _ _ _ h4 hV (Nat.cast_nonneg _)
    exact hraw.trans (by convert hprod using 1; congr 1; omega)
  have hspan : (2^54*129*PhysicalParameters.routingSide S I.precision : ℕ) ≤
      S.nnz^(54+129+SelectedLogicalBounds.sideExponent p) := by
    have h2 : (2 : ℚ)^54 ≤ (S.nnz : ℚ)^54 := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm2) _
    have hp := SelectedLogicalBounds.mul_bound _ _ _
      (SelectedLogicalBounds.mul_bound _ _ _ h2 (SelectedLogicalBounds.constant_bound S.nnz 129 hm2) (by norm_num))
      hside (Nat.cast_nonneg _)
    exact_mod_cast hp
  have heps : (I.epsilon/16)⁻¹ ≤ (S.nnz : ℚ)^(4+SelectedLogicalBounds.errorExponent p) := by
    have h16 : (16 : ℚ) ≤ (S.nnz : ℚ)^4 := by
      exact (show (16 : ℚ) = 2^4 by norm_num).le.trans
        (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm2) 4)
    have hh := SelectedLogicalBounds.error_inverse_bound p S hm hm2 hunit
    change I.epsilon⁻¹ ≤ _ at hh
    have hp := SelectedLogicalBounds.mul_bound _ _ _ h16 hh (inv_pos.mpr I.epsilon_pos).le
    rw [inv_div]
    simpa only [div_eq_mul_inv] using hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (S.nnz : ℚ) ≤ (2 : ℚ)^(P*ℓ)
    apply hpromote (a := 1) (by simp only [pow_one, le_refl])
    unfold P sourceBudgetExponent
    omega
  · apply hpromote hJ
    unfold P sourceBudgetExponent
    omega
  · intro j
    apply hpromote (by exact_mod_cast hspan)
    unfold P sourceBudgetExponent
    omega
  · apply hpromote (SelectedLogicalBounds.logical_bound p S hm hm2 hunit)
    unfold P sourceBudgetExponent
    omega
  · apply hpromote heps
    unfold P sourceBudgetExponent
    omega

#print axioms sourceInput_binary

end Maxwell.Continuum.Parameters
