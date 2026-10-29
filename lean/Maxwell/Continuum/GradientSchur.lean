import Maxwell.Continuum.CoerciveInverse

/-!
# Uniform elimination of the gradient block

The bounded positive material compression B is inverted at every real
parameter in [-1/4,1/4]. The Schur correction has the sign and parameter
monotonicity used in the finite-box count. No finite-dimensional hypothesis
is imposed on the eliminated space.
-/

noncomputable section

namespace Maxwell.Continuum.GradientSchur

set_option backward.isDefEq.respectTransparency false

open CoerciveInverse

variable {G T : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup T] [InnerProductSpace ℂ T] [CompleteSpace T]

def shift (B : G →L[ℂ] G) (ell : ℝ) : G →L[ℂ] G :=
  B + (ell : ℂ) • ContinuousLinearMap.id ℂ G

omit [CompleteSpace G] in
@[simp] theorem shift_apply (B : G →L[ℂ] G) (ell : ℝ) (x : G) :
    shift B ell x = B x + (ell : ℂ) • x := rfl

omit [CompleteSpace G] in
theorem shift_energy (B : G →L[ℂ] G) (ell : ℝ) (x : G) :
    (inner ℂ x (shift B ell x)).re = (inner ℂ x (B x)).re + ell * ‖x‖ ^ 2 := by
  rw [shift_apply, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

omit [CompleteSpace G] in
theorem shift_symmetric (B : G →L[ℂ] G) (hB : B.IsSymmetric) (ell : ℝ) :
    (shift B ell).IsSymmetric := by
  intro x y
  have hxy : inner ℂ (B x) y = inner ℂ x (B y) := hB x y
  simp only [ContinuousLinearMap.coe_coe, shift_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, hxy]

omit [CompleteSpace G] in
theorem shift_coercive (B : G →L[ℂ] G) (hB : Coercive B 1)
    (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) : Coercive (shift B ell) (3 / 4) := by
  intro x
  rw [shift_energy]
  have h := hB x
  have hp := mul_le_mul_of_nonneg_right hell (sq_nonneg ‖x‖)
  simp only [one_mul] at h
  linarith

def gradientInverse (B : G →L[ℂ] G) (hB : Coercive B 1)
    (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) : G →L[ℂ] G :=
  inverse (shift B ell) (by norm_num : (0 : ℝ) < 3 / 4) (shift_coercive B hB ell hell)

@[simp] theorem shift_gradientInverse (B : G →L[ℂ] G) (hB : Coercive B 1)
    (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) (x : G) :
    shift B ell (gradientInverse B hB ell hell x) = x := apply_inverse _ _ _ _

@[simp] theorem gradientInverse_shift (B : G →L[ℂ] G) (hB : Coercive B 1)
    (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) (x : G) :
    gradientInverse B hB ell hell (shift B ell x) = x := inverse_apply _ _ _ _

theorem gradientInverse_norm_le (B : G →L[ℂ] G) (hB : Coercive B 1)
    (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) : ‖gradientInverse B hB ell hell‖ ≤ 4 / 3 := by
  simpa [gradientInverse] using
    norm_inverse (shift B ell) (by norm_num : (0 : ℝ) < 3 / 4) (shift_coercive B hB ell hell)

theorem gradientInverse_symmetric (B : G →L[ℂ] G) (hB : Coercive B 1)
    (hs : B.IsSymmetric) (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    (gradientInverse B hB ell hell).IsSymmetric :=
  inverse_symmetric _ _ _ (shift_symmetric B hs ell)

theorem gradientInverse_nonnegative (B : G →L[ℂ] G) (hB : Coercive B 1)
    (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) (x : G) :
    0 ≤ (inner ℂ x (gradientInverse B hB ell hell x)).re := inverse_nonnegative _ _ _ _

theorem gradientInverse_antitone (B : G →L[ℂ] G) (hB : Coercive B 1)
    (hs : B.IsSymmetric) (ell μ : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (hμ : -(1 / 4 : ℝ) ≤ μ) (hle : ell ≤ μ) (x : G) :
    (inner ℂ x (gradientInverse B hB μ hμ x)).re ≤
      (inner ℂ x (gradientInverse B hB ell hell x)).re := by
  apply inverse_antitone _ _ _ _ _ _ (shift_symmetric B hs ell) _ x
  intro y
  rw [shift_energy, shift_energy]
  linarith [mul_le_mul_of_nonneg_right hle (sq_nonneg ‖y‖)]

/-- The positive correction ε_tg (B+ell)⁻¹ ε_gt. -/
def correction (B : G →L[ℂ] G) (hB : Coercive B 1) (E : T →L[ℂ] G)
    (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) : T →L[ℂ] T :=
  E.adjoint.comp ((gradientInverse B hB ell hell).comp E)

theorem correction_energy (B : G →L[ℂ] G) (hB : Coercive B 1) (E : T →L[ℂ] G)
    (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) (x : T) :
    inner ℂ x (correction B hB E ell hell x) =
      inner ℂ (E x) (gradientInverse B hB ell hell (E x)) := by
  simp only [correction, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

theorem correction_symmetric (B : G →L[ℂ] G) (hB : Coercive B 1) (hs : B.IsSymmetric)
    (E : T →L[ℂ] G) (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    (correction B hB E ell hell).IsSymmetric := by
  intro x y
  change inner ℂ (E.adjoint (gradientInverse B hB ell hell (E x))) y =
    inner ℂ x (E.adjoint (gradientInverse B hB ell hell (E y)))
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact gradientInverse_symmetric B hB hs ell hell (E x) (E y)

def boundedPart (B : G →L[ℂ] G) (hB : Coercive B 1)
    (D : T →L[ℂ] T) (E : T →L[ℂ] G) (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) : T →L[ℂ] T :=
  -D - (ell : ℂ) • ContinuousLinearMap.id ℂ T + correction B hB E ell hell

theorem boundedPart_symmetric (B : G →L[ℂ] G) (hB : Coercive B 1) (hs : B.IsSymmetric)
    (D : T →L[ℂ] T) (hD : D.IsSymmetric) (E : T →L[ℂ] G)
    (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    (boundedPart B hB D E ell hell).IsSymmetric := by
  intro x y
  have hd : inner ℂ (D x) y = inner ℂ x (D y) := hD x y
  have hr : inner ℂ (correction B hB E ell hell x) y =
      inner ℂ x (correction B hB E ell hell y) := correction_symmetric B hB hs E ell hell x y
  change inner ℂ (-D x - (ell : ℂ) • x + correction B hB E ell hell x) y =
    inner ℂ x (-D y - (ell : ℂ) • y + correction B hB E ell hell y)
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hd, hr]

theorem boundedPart_energy (B : G →L[ℂ] G) (hB : Coercive B 1)
    (D : T →L[ℂ] T) (E : T →L[ℂ] G) (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) (x : T) :
    (inner ℂ x (boundedPart B hB D E ell hell x)).re =
      -(inner ℂ x (D x)).re - ell * ‖x‖ ^ 2 +
        (inner ℂ (E x) (gradientInverse B hB ell hell (E x))).re := by
  change (inner ℂ x (-D x - (ell : ℂ) • x + correction B hB E ell hell x)).re = _
  rw [inner_add_right, inner_sub_right, inner_neg_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, correction_energy]
  simp [← Complex.ofReal_pow]

theorem boundedPart_lower (B : G →L[ℂ] G) (hB : Coercive B 1)
    (D : T →L[ℂ] T) (hD : ∀ x, (inner ℂ x (D x)).re ≤ 25 * ‖x‖ ^ 2)
    (E : T →L[ℂ] G) (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) (hell' : ell ≤ 1 / 4) (x : T) :
    -26 * ‖x‖ ^ 2 ≤ (inner ℂ x (boundedPart B hB D E ell hell x)).re := by
  rw [boundedPart_energy]
  have hnonneg := gradientInverse_nonnegative B hB ell hell (E x)
  have hupper := hD x
  have hmul := mul_le_mul_of_nonneg_right hell' (sq_nonneg ‖x‖)
  nlinarith [sq_nonneg ‖x‖]

/-- The strict -ellI term remains after the positive Schur correction decreases. -/
theorem boundedPart_strict_antitone (B : G →L[ℂ] G) (hB : Coercive B 1)
    (hs : B.IsSymmetric) (D : T →L[ℂ] T) (E : T →L[ℂ] G)
    (ell μ : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) (hμ : -(1 / 4 : ℝ) ≤ μ)
    (hle : ell ≤ μ) (x : T) :
    (inner ℂ x (boundedPart B hB D E μ hμ x)).re ≤
      (inner ℂ x (boundedPart B hB D E ell hell x)).re - (μ - ell) * ‖x‖ ^ 2 := by
  rw [boundedPart_energy, boundedPart_energy]
  have h := gradientInverse_antitone B hB hs ell μ hell hμ hle (E x)
  nlinarith

end Maxwell.Continuum.GradientSchur
