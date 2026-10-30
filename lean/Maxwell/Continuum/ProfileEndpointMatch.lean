import Maxwell.Continuum.ProfileFiniteSeries

/-! Exact endpoint value and derivative matching of a polynomial profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Set

def endpointMatch (f : ℝ → ℝ) (t : ℝ) : ℝ := f t-f 1-deriv f 1*(t-1)

set_option backward.isDefEq.respectTransparency false in
theorem endpointMatch_hasDerivAt {f : ℝ → ℝ} (hf : Differentiable ℝ f) (t : ℝ) :
    HasDerivAt (endpointMatch f) (deriv f t-deriv f 1) t := by
  have h := ((hf t).hasDerivAt.sub_const (f 1)).sub
    (((hasDerivAt_id t).sub_const 1).const_mul (deriv f 1))
  convert h using 1
  · funext x
    rfl
  · ring

theorem endpointMatch_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (endpointMatch f) := by
  exact (hf.sub contDiff_const).sub (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem endpointMatch_value (f : ℝ → ℝ) : endpointMatch f 1=0 := by
  simp only [endpointMatch, sub_self, mul_zero]

theorem endpointMatch_derivative {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (endpointMatch f) 1=0 := by rw [(endpointMatch_hasDerivAt hf 1).deriv, sub_self]

theorem endpointMatch_error {f : ℝ → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, |radial t-f t| ≤ η)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, |deriv radial t-deriv f t| ≤ η)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |radial t-endpointMatch f t| ≤ 3*η := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hv := hf 1 h1
  have hvd := hd 1 h1
  rw [radial_zero le_rfl, zero_sub, abs_neg] at hv
  rw [radial_endpoint_derivative, zero_sub, abs_neg] at hvd
  have ht1 : |t-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  calc
    _ = |(radial t-f t)+f 1+deriv f 1*(t-1)| := by unfold endpointMatch; congr 1; ring
    _ ≤ |radial t-f t|+|f 1|+|deriv f 1| * |t-1| := by
      simpa only [abs_mul] using (abs_add_le (radial t-f t+f 1) (deriv f 1*(t-1))).trans
        (add_le_add (abs_add_le (radial t-f t) (f 1)) (le_refl |deriv f 1*(t-1)|))
    _ ≤ η+η+η*1 := add_le_add (add_le_add (hf t ht) hv)
      (mul_le_mul hvd ht1 (abs_nonneg _) hη)
    _ = _ := by ring

theorem endpointMatch_derivative_error {f : ℝ → ℝ} (hf : Differentiable ℝ f) {η : ℝ}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, |deriv radial t-deriv f t| ≤ η)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |deriv radial t-deriv (endpointMatch f) t| ≤ 2*η := by
  have hvd := hd 1 (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  rw [radial_endpoint_derivative, zero_sub, abs_neg] at hvd
  rw [(endpointMatch_hasDerivAt hf t).deriv]
  calc
    _ = |(deriv radial t-deriv f t)+deriv f 1| := by congr 1; ring
    _ ≤ |deriv radial t-deriv f t|+|deriv f 1| := abs_add_le _ _
    _ ≤ _ := by linarith [hd t ht]

#print axioms endpointMatch_error
#print axioms endpointMatch_derivative_error

end Maxwell.Continuum.Profile
