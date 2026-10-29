import Maxwell.Composition.PhysicalParameters

/-! A single exact rational physical tolerance pays both logical residual
transport and the finite original-coordinate readout allowance. -/
namespace Maxwell.Composition.PhysicalAccuracy
open Maxwell.Logical

def residualFactor (S : Source.SparseSystem) (precision : ℕ) : ℕ :=
  routedResidualFactor S precision (1024*PhysicalParameters.routingSide S precision)

theorem residualFactor_eq (S : Source.SparseSystem) (precision : ℕ) :
    residualFactor S precision = SourceRecovery.residualFactor S precision := by
  rw [residualFactor,PhysicalParameters.routingSide_eq]
  rfl

def denominator (S : Source.SparseSystem) (precision : ℕ) : ℕ :=
  max 1 (residualFactor S precision) * max 1 (S.nnz^2)

theorem denominator_ge_one (S : Source.SparseSystem) (precision : ℕ) :
    1 ≤ denominator S precision := by
  have h1 : 1 ≤ max 1 (residualFactor S precision) := le_max_left _ _
  have h2 : 1 ≤ max 1 (S.nnz^2) := le_max_left _ _
  unfold denominator
  nlinarith

def epsilon (S : Source.SparseSystem) (precision : ℕ) (eta : ℚ) : ℚ :=
  min (1/2) (eta/(denominator S precision : ℚ))

theorem epsilon_pos (S : Source.SparseSystem) (precision : ℕ) (eta : ℚ) (heta : 0 < eta) :
    0 < epsilon S precision eta := by
  have hd : (0 : ℚ) < denominator S precision := by exact_mod_cast denominator_ge_one S precision
  exact lt_min (by norm_num) (div_pos heta hd)

theorem epsilon_le_half (S : Source.SparseSystem) (precision : ℕ) (eta : ℚ) :
    epsilon S precision eta ≤ 1/2 := min_le_left _ _

theorem epsilon_denominator (S : Source.SparseSystem) (precision : ℕ) (eta : ℚ) :
    epsilon S precision eta*(denominator S precision : ℚ) ≤ eta := by
  have hd : (0 : ℚ) < denominator S precision := by exact_mod_cast denominator_ge_one S precision
  exact (le_div_iff₀ hd).mp (min_le_right _ _)

theorem epsilon_residualFactor (S : Source.SparseSystem) (precision : ℕ) (eta : ℚ) (heta : 0 < eta) :
    (SourceRecovery.residualFactor S precision : ℚ)*epsilon S precision eta ≤ eta := by
  have hr : residualFactor S precision ≤ denominator S precision := by
    apply le_trans (le_max_right 1 _)
    exact Nat.le_mul_of_pos_right _ (by omega)
  have h := mul_le_mul_of_nonneg_left (show (residualFactor S precision : ℚ) ≤ denominator S precision by exact_mod_cast hr)
    (epsilon_pos S precision eta heta).le
  rw [residualFactor_eq] at h
  have he := epsilon_denominator S precision eta
  nlinarith

theorem epsilon_nnz_sq (S : Source.SparseSystem) (precision : ℕ) (eta : ℚ) (heta : 0 < eta) :
    epsilon S precision eta*(S.nnz : ℚ)^2 ≤ eta := by
  have hm : S.nnz^2 ≤ denominator S precision := by
    apply le_trans (le_max_right 1 _)
    exact Nat.le_mul_of_pos_left _ (by omega)
  have h := mul_le_mul_of_nonneg_left (show ((S.nnz : ℚ)^2) ≤ denominator S precision by exact_mod_cast hm)
    (epsilon_pos S precision eta heta).le
  exact h.trans (epsilon_denominator S precision eta)

theorem source_norm_le_nnz (S : Source.SparseSystem) (precision : ℕ)
    (hunit : IsUnit (Source.realMatrix S)) (hb : S.source ≠ 0) (hm : 0 < S.nnz) :
    ‖SourceSubdivision.source S precision‖ ≤ (S.nnz : ℝ) := by
  apply (SourceSubdivision.source_norm_bounds S hb precision).2.trans
  apply (Real.sqrt_le_iff).mpr
  have hn : (S.n : ℝ) ≤ S.nnz := by exact_mod_cast Source.dimension_le_nnz S hunit
  have hm1 : (1 : ℝ) ≤ S.nnz := by exact_mod_cast hm
  exact ⟨by positivity,by nlinarith⟩

/-- The conservative squared-nnz allowance absorbs the actual source norm
and the constant from the fixed-message decoder. -/
theorem selected_read_budget (S : Source.SparseSystem) (precision : ℕ) (eta : ℚ) (heta : 0 < eta)
    (hunit : IsUnit (Source.realMatrix S)) (hb : S.source ≠ 0) (hm : 0 < S.nnz) :
    13*(epsilon S precision eta : ℝ)*‖SourceSubdivision.source S precision‖/4096 ≤
      (eta : ℝ)/(16*S.nnz) := by
  have he : (epsilon S precision eta : ℝ)*(S.nnz : ℝ)^2 ≤ eta := by
    exact_mod_cast epsilon_nnz_sq S precision eta heta
  have hε : (0 : ℝ) ≤ epsilon S precision eta := by exact_mod_cast (epsilon_pos S precision eta heta).le
  have hη : (0 : ℝ) ≤ eta := by exact_mod_cast heta.le
  have hg := source_norm_le_nnz S precision hunit hb hm
  have hprod := mul_le_mul_of_nonneg_left hg hε
  have hm0 : (0 : ℝ) < S.nnz := by exact_mod_cast hm
  have hprod' := mul_le_mul_of_nonneg_right hprod hm0.le
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16*S.nnz)).mpr
  nlinarith

end Maxwell.Composition.PhysicalAccuracy
