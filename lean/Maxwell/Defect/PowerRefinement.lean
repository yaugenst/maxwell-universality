import Maxwell.Defect.RankOneSpectral
import Maxwell.Defect.RationalResidual
import Maxwell.Defect.NormalizedLocalEigenvector

/-! Polynomial power filtering of a fixed simple spectral line. -/
namespace Maxwell.Defect
open InnerProductSpace Module.End Matrix

theorem norm_power_difference_le {A : Type*} [NormedRing A] [NormOneClass A]
    (a b : A) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 2) (N : ℕ) :
    ‖a ^ N - b ^ N‖ ≤ (N : ℝ) * 2 ^ N * ‖a - b‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hid : a ^ (N + 1) - b ^ (N + 1) =
          (a - b) * a ^ N + b * (a ^ N - b ^ N) := by
        rw [pow_succ', pow_succ', sub_mul, mul_sub]
        abel
      have hap : ‖a ^ N‖ ≤ 1 := (norm_pow_le _ _).trans
        (by simpa using pow_le_pow_left₀ (norm_nonneg _) ha N)
      calc
        _ ≤ ‖a - b‖ * ‖a ^ N‖ + ‖b‖ * ‖a ^ N - b ^ N‖ := by
          rw [hid]
          exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ ‖a - b‖ * 1 + 2 * ((N : ℝ) * 2 ^ N * ‖a - b‖) := by gcongr
        _ ≤ _ := by
          rw [Nat.cast_add, Nat.cast_one, pow_succ]
          have hp : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
          nlinarith [norm_nonneg (a - b)]

theorem normalize_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x - y‖ / ‖y‖ := by
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hunit : ‖NormedSpace.normalize y‖ = 1 := NormedSpace.norm_normalize hy
  by_cases hx : x = 0
  · subst x
    simp only [NormedSpace.normalize_zero_eq_zero, zero_sub, norm_neg, hunit]
    rw [mul_div_cancel_right₀ _ hypos.ne']
    norm_num
  · have hs : ‖y‖⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hypos.ne') hx
    have hh := normalize_sub_unit_le (‖y‖⁻¹ • x) (NormedSpace.normalize y) hs hunit
    rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hypos)] at hh
    have he : ‖y‖⁻¹ • x - NormedSpace.normalize y = ‖y‖⁻¹ • (x - y) := by
      rw [NormedSpace.normalize, smul_sub]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hypos)] at hh
    convert hh using 1
    ring

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def modeFilter (S : E →L[ℝ] E) (target scale : ℝ) : E →L[ℝ] E :=
  1 - scale • (S - target • 1) ^ 2

def scalarModeFilter (target scale x : ℝ) : ℝ := 1 - scale * (x - target) ^ 2

theorem modeFilter_coordinate (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target scale : ℝ) (x : E) (i : Fin (Module.finrank ℝ E)) :
    (hS.eigenvectorBasis rfl).repr (modeFilter S target scale x) i =
      scalarModeFilter target scale (hS.eigenvalues rfl i) *
        (hS.eigenvectorBasis rfl).repr x i := by
  let e := (hS.eigenvectorBasis rfl).repr
  have hc (y : E) : e (S y) i = hS.eigenvalues rfl i * e y i :=
    hS.eigenvectorBasis_apply_self_apply rfl y i
  change e (modeFilter S target scale x) i = _
  simp only [modeFilter, scalarModeFilter, pow_two, _root_.sub_apply,
    one_apply_eq_self, _root_.smul_apply,
    mul_apply_eq_comp, map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, hc]
  ring

theorem modeFilter_power_coordinate (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target scale : ℝ) (x : E) (N : ℕ) (i : Fin (Module.finrank ℝ E)) :
    (hS.eigenvectorBasis rfl).repr (((modeFilter S target scale) ^ N) x) i =
      scalarModeFilter target scale (hS.eigenvalues rfl i) ^ N *
        (hS.eigenvectorBasis rfl).repr x i := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ', mul_apply_eq_comp, modeFilter_coordinate, ih, pow_succ']
      ring

set_option maxHeartbeats 600000 in
/-- Filtering damps every complementary spectral coordinate at a fixed
geometric rate; the projection is the actual eigenspace projection. -/
theorem modeFilter_power_error (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target scale μ β : ℝ) (hβ : 0 ≤ β)
    (hfilter : ∀ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i ≠ μ →
      |scalarModeFilter target scale (hS.eigenvalues rfl i)| ≤ β)
    (x : E) (N : ℕ) :
    ‖((modeFilter S target scale) ^ N) x -
      scalarModeFilter target scale μ ^ N • selectedProjection S μ x‖ ≤ β ^ N * ‖x‖ := by
  classical
  let e := (hS.eigenvectorBasis rfl).repr
  let y := ((modeFilter S target scale) ^ N) x -
    scalarModeFilter target scale μ ^ N • selectedProjection S μ x
  have hcoord (i : Fin (Module.finrank ℝ E)) : |e y i| ≤ β ^ N * |e x i| := by
    dsimp only [y, e]
    rw [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply,
      modeFilter_power_coordinate, spectral_coordinates_projection]
    simp only [smul_eq_mul, spectralP_apply]
    by_cases hi : hS.eigenvalues rfl i = μ
    · simp only [hi, ite_true, sub_self, abs_zero]
      positivity
    · simp only [hi, ite_false, mul_zero, sub_zero, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hfilter i hi) N)
        (abs_nonneg _)
  have hs : ‖e y‖ ^ 2 ≤ (β ^ N) ^ 2 * ‖e x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := pow_le_pow_left₀ (abs_nonneg (e y i)) (hcoord i) 2
    simpa only [sq_abs, mul_pow] using hh
  rw [e.norm_map, e.norm_map] at hs
  change ‖y‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg hβ _) (norm_nonneg _))).mp
  simpa only [mul_pow] using hs

omit [FiniteDimensional ℝ E] in
theorem modeFilter_eigen (S : E →L[ℝ] E) (u : E) (μ target scale : ℝ)
    (he : S u = μ • u) : modeFilter S target scale u = scalarModeFilter target scale μ • u := by
  have hh : (S - target • 1) u = (μ - target) • u := by
    simp only [_root_.sub_apply, _root_.smul_apply,
      one_apply_eq_self, he, sub_smul]
  have hh2 : (((S - target • 1) ^ 2 : E →L[ℝ] E)) u = (μ - target) ^ 2 • u := by
    rw [pow_two, mul_apply_eq_comp, hh, map_smul, hh, smul_smul, pow_two]
  rw [modeFilter, _root_.sub_apply, one_apply_eq_self, _root_.smul_apply, hh2, smul_smul,
    scalarModeFilter, sub_smul, one_smul]

theorem modeFilter_norm_le_one (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target scale : ℝ)
    (hfilter : ∀ i : Fin (Module.finrank ℝ E),
      |scalarModeFilter target scale (hS.eigenvalues rfl i)| ≤ 1) :
    ‖modeFilter S target scale‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  let e := (hS.eigenvectorBasis rfl).repr
  have hs : ‖e (modeFilter S target scale x)‖ ^ 2 ≤ ‖e x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    rw [show e (modeFilter S target scale x) i =
      scalarModeFilter target scale (hS.eigenvalues rfl i) * e x i from
        modeFilter_coordinate S hS target scale x i, mul_pow]
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hfilter i) 2
    simp only [sq_abs, one_pow] at hh
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (one_mul _)
  rw [e.norm_map, e.norm_map] at hs
  simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

set_option maxHeartbeats 600000 in
theorem normalized_modeFilter_error (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target scale μ β : ℝ) (hβ : 0 ≤ β)
    (hα : 0 < scalarModeFilter target scale μ)
    (hfilter : ∀ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i ≠ μ →
      |scalarModeFilter target scale (hS.eigenvalues rfl i)| ≤ β)
    (x : E) (hp : selectedProjection S μ x ≠ 0) (N : ℕ) :
    ‖NormedSpace.normalize (((modeFilter S target scale) ^ N) x) -
      NormedSpace.normalize (selectedProjection S μ x)‖ ≤
        (2 * ‖x‖ / ‖selectedProjection S μ x‖) *
          (β / scalarModeFilter target scale μ) ^ N := by
  have hαN := pow_pos hα N
  have hpn := norm_pos_iff.mpr hp
  have hnonzero : scalarModeFilter target scale μ ^ N • selectedProjection S μ x ≠ 0 :=
    smul_ne_zero hαN.ne' hp
  have hh := normalize_sub_le (((modeFilter S target scale) ^ N) x)
    (scalarModeFilter target scale μ ^ N • selectedProjection S μ x) hnonzero
  rw [NormedSpace.normalize_smul_of_pos hαN, norm_smul, Real.norm_eq_abs,
    abs_of_pos hαN] at hh
  have he := modeFilter_power_error S hS target scale μ β hβ hfilter x N
  calc
    _ ≤ 2 * ‖((modeFilter S target scale) ^ N) x -
        scalarModeFilter target scale μ ^ N • selectedProjection S μ x‖ /
          (scalarModeFilter target scale μ ^ N * ‖selectedProjection S μ x‖) := hh
    _ ≤ 2 * (β ^ N * ‖x‖) /
          (scalarModeFilter target scale μ ^ N * ‖selectedProjection S μ x‖) := by gcongr
    _ = _ := by rw [div_pow]; field_simp

set_option maxHeartbeats 600000 in
/-- Rational matrix approximations may be substituted in every filtering
step. Their accumulated error is controlled explicitly before normalization. -/
theorem approximate_modeFilter_error (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target scale μ β ε : ℝ) (hβ : 0 ≤ β)
    (hα : 0 < scalarModeFilter target scale μ)
    (hfilter : ∀ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i ≠ μ →
      |scalarModeFilter target scale (hS.eigenvalues rfl i)| ≤ β)
    (hFnorm : ‖modeFilter S target scale‖ ≤ 1)
    (B : E →L[ℝ] E) (hBnorm : ‖B‖ ≤ 2) (hB : ‖modeFilter S target scale - B‖ ≤ ε)
    (x : E) (hp : selectedProjection S μ x ≠ 0) (N : ℕ) :
    ‖NormedSpace.normalize ((B ^ N) x) - NormedSpace.normalize (selectedProjection S μ x)‖ ≤
      (2 * ‖x‖ / ‖selectedProjection S μ x‖) *
        (((N : ℝ) * 2 ^ N * ε) / scalarModeFilter target scale μ ^ N +
          (β / scalarModeFilter target scale μ) ^ N) := by
  have : Nontrivial E := ⟨⟨selectedProjection S μ x, 0, hp⟩⟩
  have hαN := pow_pos hα N
  have hpn := norm_pos_iff.mpr hp
  have hnonzero : scalarModeFilter target scale μ ^ N • selectedProjection S μ x ≠ 0 :=
    smul_ne_zero hαN.ne' hp
  have hh := normalize_sub_le ((B ^ N) x)
    (scalarModeFilter target scale μ ^ N • selectedProjection S μ x) hnonzero
  rw [NormedSpace.normalize_smul_of_pos hαN, norm_smul, Real.norm_eq_abs,
    abs_of_pos hαN] at hh
  have herr : ‖(B ^ N) x - scalarModeFilter target scale μ ^ N • selectedProjection S μ x‖ ≤
      ((N : ℝ) * 2 ^ N * ε + β ^ N) * ‖x‖ := by
    calc
      _ ≤ ‖(B ^ N) x - ((modeFilter S target scale) ^ N) x‖ +
          ‖((modeFilter S target scale) ^ N) x -
            scalarModeFilter target scale μ ^ N • selectedProjection S μ x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ((N : ℝ) * 2 ^ N * ε) * ‖x‖ + β ^ N * ‖x‖ := by
        apply add_le_add _ (modeFilter_power_error S hS target scale μ β hβ hfilter x N)
        rw [← _root_.sub_apply]
        apply (ContinuousLinearMap.le_opNorm _ _).trans
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [norm_sub_rev]
        exact (norm_power_difference_le _ B hFnorm hBnorm N).trans
          (mul_le_mul_of_nonneg_left hB (by positivity))
      _ = _ := by ring
  calc
    _ ≤ 2 * ‖(B ^ N) x - scalarModeFilter target scale μ ^ N • selectedProjection S μ x‖ /
        (scalarModeFilter target scale μ ^ N * ‖selectedProjection S μ x‖) := hh
    _ ≤ 2 * (((N : ℝ) * 2 ^ N * ε + β ^ N) * ‖x‖) /
        (scalarModeFilter target scale μ ^ N * ‖selectedProjection S μ x‖) := by gcongr
    _ = _ := by rw [div_pow]; field_simp

end Operator

section Rational
variable {n : ℕ}

def rationalModeFilter (T : Matrix (Fin n) (Fin n) ℚ) (target scale : ℚ) :
    Matrix (Fin n) (Fin n) ℚ := 1 - scale • (T - target • 1) ^ 2

theorem rationalModeFilter_operator (T : Matrix (Fin n) (Fin n) ℚ) (target scale : ℚ) :
    rationalOperator (rationalModeFilter T target scale) =
      modeFilter (rationalOperator T) target scale := by
  simp only [rationalModeFilter, modeFilter, map_sub, map_one, rationalOperator_smul, map_pow]

/-- One matrix-vector product per power step, with fixed matrix dimension. -/
def rationalPowerAction (T : Matrix (Fin n) (Fin n) ℚ) : ℕ → (Fin n → ℚ) → (Fin n → ℚ)
  | 0, v => v
  | N + 1, v => T *ᵥ rationalPowerAction T N v

theorem rationalVector_mulVec (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    rationalVector (T *ᵥ v) = rationalOperator T (rationalVector v) := by
  ext i
  change ((∑ j, T i j * v j : ℚ) : ℝ) = ∑ j, (T i j : ℝ) * (v j : ℝ)
  simp

theorem rationalPowerAction_operator (T : Matrix (Fin n) (Fin n) ℚ) (N : ℕ)
    (v : Fin n → ℚ) : rationalVector (rationalPowerAction T N v) =
      ((rationalOperator T) ^ N) (rationalVector v) := by
  induction N with
  | zero => simp [rationalPowerAction]
  | succ N ih =>
      rw [rationalPowerAction, rationalVector_mulVec, ih, pow_succ', mul_apply_eq_comp]

end Rational
end Maxwell.Defect
