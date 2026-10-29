import Maxwell.Source
import Maxwell.Logical.Rounding

/-! Typed coordinate selection and exact normalization reversal.
This module proves the final algebraic/read-precision interface. The actual
source-to-routed-graph compiler must construct its `coordinate` map; an
arbitrary selector is not presented as that missing construction.
-/

namespace Maxwell.Logical

structure DecoderPlan (sourceDimension logicalDimension : ℕ) where
  coordinate : Fin sourceDimension → Fin logicalDimension
  scale : ℚ

namespace DecoderPlan

def select {n d : ℕ} (plan : DecoderPlan n d) {K : Type*} (u : Fin d → K) : Fin n → K :=
  fun i => u (plan.coordinate i)

def decode {n d : ℕ} (plan : DecoderPlan n d) (u : Fin d → ℚ) : Fin n → ℚ :=
  fun i => plan.scale * u (plan.coordinate i)

noncomputable def realDecode {n d : ℕ} (plan : DecoderPlan n d)
    (u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => (plan.scale : ℝ) * u (plan.coordinate i)

theorem rational_decode {n d : ℕ} (plan : DecoderPlan n d) (u : Fin d → ℚ) :
    Source.rationalVector (plan.decode u) = plan.realDecode (Source.rationalVector u) := by
  ext i
  simp [Source.rationalVector, decode, realDecode]

/-- Explicit coordinatewise amplification by the actual short rational scale. -/
theorem coordinate_error {n d : ℕ} (plan : DecoderPlan n d)
    (u v : Fin d → ℝ) (e : ℝ) (i : Fin n)
    (h : |u (plan.coordinate i) - v (plan.coordinate i)| ≤ e) :
    |(plan.scale : ℝ) * u (plan.coordinate i) -
        (plan.scale : ℝ) * v (plan.coordinate i)| ≤ |(plan.scale : ℝ)| * e := by
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- Every prescribed coordinate may carry its own worst-case error.
The bound charges the complete number of decoded coordinates. -/
theorem realDecode_error {n d : ℕ} (plan : DecoderPlan n d)
    (u v : EuclideanSpace ℝ (Fin d)) (e : ℝ) (he : 0 ≤ e)
    (h : ∀ i, |u (plan.coordinate i) - v (plan.coordinate i)| ≤ e) :
    ‖plan.realDecode u - plan.realDecode v‖ ≤
      |(plan.scale : ℝ)| * Real.sqrt n * e := by
  have hsq : ‖plan.realDecode u - plan.realDecode v‖ ^ 2 ≤
      (|(plan.scale : ℝ)| * Real.sqrt n * e) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin n, (|(plan.scale : ℝ)| * e) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := plan.coordinate_error u v e i (h i)
        have hs := (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) he)).mpr hi
        simpa [sq_abs, realDecode] using hs
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [mul_pow]
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

end DecoderPlan

section Normalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalization_residual_identity (M : E →L[ℝ] E) (b u : E)
    (lambda beta : ℝ) (hb : beta ≠ 0) :
    M ((beta / lambda) • u) - b =
      beta • ((lambda⁻¹ • M) u - beta⁻¹ • b) := by
  simp [map_smul, smul_sub, smul_smul, div_eq_mul_inv, hb]

/-- Reversing normalization preserves the relative residual exactly. -/
theorem normalization_residual_transfer (M : E →L[ℝ] E) (b u : E)
    (lambda beta eta : ℝ) (hb : beta ≠ 0)
    (h : ‖(lambda⁻¹ • M) u - beta⁻¹ • b‖ ≤ eta * ‖beta⁻¹ • b‖) :
    ‖M ((beta / lambda) • u) - b‖ ≤ eta * ‖b‖ := by
  rw [normalization_residual_identity M b u lambda beta hb, norm_smul,
    Real.norm_eq_abs]
  have hs := mul_le_mul_of_nonneg_left h (abs_nonneg beta)
  calc
    |beta| * ‖(lambda⁻¹ • M) u - beta⁻¹ • b‖ ≤
        |beta| * (eta * ‖beta⁻¹ • b‖) := hs
    _ = eta * ‖b‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
      have hab : |beta| ≠ 0 := abs_ne_zero.mpr hb
      field_simp

end Normalization

/-- Concrete binding to the paper's square rational source interface. -/
theorem source_residual_transfer (S : Source.SparseSystem) (lambda beta : ℚ)
    (hb : beta ≠ 0) (u : Fin S.n → ℚ) (eta : ℝ)
    (h : ‖(((lambda : ℝ)⁻¹) • Source.operator S) (Source.rationalVector u) -
          ((beta : ℝ)⁻¹) • Source.rhs S‖ ≤
        eta * ‖((beta : ℝ)⁻¹) • Source.rhs S‖) :
    Source.ResidualTarget S eta (fun i => (beta / lambda) * u i) := by
  have hbr : (beta : ℝ) ≠ 0 := by exact_mod_cast hb
  have hresult := normalization_residual_transfer (Source.operator S) (Source.rhs S)
    (Source.rationalVector u) lambda beta eta hbr h
  have hv : Source.rationalVector (fun i => (beta / lambda) * u i) =
      ((beta : ℝ) / (lambda : ℝ)) • Source.rationalVector u := by
    ext i
    simp [Source.rationalVector]
  simpa [Source.ResidualTarget, hv] using hresult

end Maxwell.Logical
