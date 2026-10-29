import Maxwell.Continuum.TopEigenPerturbationInterlacing
import Maxwell.Continuum.TopEigenPerturbationReality

/-! Quantitative complement and residual-gap bounds after a bounded
self-adjoint perturbation of a positive reference operator. The perturbed
operator itself need not be positive or compact. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.TopEigenPerturbation.Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

theorem perturbed_complement_energy_upper (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64)
    (hEs : E.IsSymmetric) (f : H) (hf : inner ℂ (D.vector E hE) f = 0) :
    (inner ℂ f ((A + E) f)).re ≤ (mu - d + ‖E‖) * ‖f‖ ^ 2 := by
  have hl : mu - d + ‖E‖ ≤ (D.eigenvalue E hE).re := by
    have h := D.eigenvalue_error E hE
    rw [← D.eigenvalue_real E hE hEs, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    linarith [(abs_le.mp h).1, D.gap_pos]
  apply upper_on_new_complement (A + E) (D.symmetric.add hEs) u (D.vector E hE)
    (D.vector_norm E hE) (D.eigenvalue E hE).re (mu - d + ‖E‖)
    (by rw [D.eigenvalue_real E hE hEs]; exact D.vector_eigen E hE)
    hl (D.vector_coefficient_ne_zero E hE) _ f hf
  intro x hx
  have he : (inner ℂ x (E x)).re ≤ ‖E‖ * ‖x‖ ^ 2 := by
    change RCLike.re (inner ℂ x (E x)) ≤ _
    exact (re_inner_le_norm (𝕜 := ℂ) x (E x)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left (E.le_opNorm x) (norm_nonneg x)])
  simp only [add_apply, inner_add_right, Complex.add_re]
  nlinarith [D.complement_energy x hx]

theorem perturbed_complement_energy_abs (hAp : A.IsPositive)
    (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric)
    (f : H) (hf : inner ℂ (D.vector E hE) f = 0) :
    |(inner ℂ f ((A + E) f)).re| ≤ (mu - d + ‖E‖) * ‖f‖ ^ 2 := by
  rw [abs_le]
  refine ⟨?_, D.perturbed_complement_energy_upper E hE hEs f hf⟩
  have ha : 0 ≤ (inner ℂ f (A f)).re := hAp.re_inner_nonneg_right f
  have he : -(‖E‖ * ‖f‖ ^ 2) ≤ (inner ℂ f (E f)).re := by
    have hnorm := norm_inner_le_norm (𝕜 := ℂ) f (E f)
    have hm := mul_le_mul_of_nonneg_left (E.le_opNorm f) (norm_nonneg f)
    have hr := (abs_le.mp (Complex.abs_re_le_norm (inner ℂ f (E f)))).1
    nlinarith
  simp only [add_apply, inner_add_right, Complex.add_re]
  have hd : 0 ≤ (mu - d) * ‖f‖ ^ 2 :=
    mul_nonneg (sub_nonneg.mpr D.gap_le_mu) (sq_nonneg _)
  nlinarith

theorem perturbed_complement_norm (hAp : A.IsPositive)
    (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric)
    (f : H) (hf : inner ℂ (D.vector E hE) f = 0) :
    ‖(A + E) f‖ ≤ (mu - d + ‖E‖) * ‖f‖ := by
  let K := RankOneBand.highSpace (D.vector E hE)
  let C := Compression.compress K (A + E)
  have hs : C.IsSymmetric := Compression.compress_symmetric K (A + E) (D.symmetric.add hEs)
  have hb : 0 ≤ mu - d + ‖E‖ := by linarith [D.gap_le_mu, norm_nonneg E]
  have hc : ‖C‖ ≤ mu - d + ‖E‖ := by
    apply symmetric_norm_le_of_energy C hs _ hb
    intro x
    rw [Compression.inner_compress]
    exact D.perturbed_complement_energy_abs hAp E hE hEs x.val
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property)
  have hfK : f ∈ K := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hf
  have hSf : (A + E) f ∈ K := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have h : inner ℂ ((A + E) (D.vector E hE)) f =
        inner ℂ (D.vector E hE) ((A + E) f) := (D.symmetric.add hEs) (D.vector E hE) f
    rw [D.vector_eigen, inner_smul_left, hf, mul_zero] at h
    exact h.symm
  have he : (C ⟨f, hfK⟩ : H) = (A + E) f :=
    K.starProjection_eq_self_iff.mpr hSf
  have hn := C.le_opNorm ⟨f, hfK⟩
  change ‖(C ⟨f, hfK⟩ : H)‖ ≤ ‖C‖ * ‖f‖ at hn
  rw [he] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg f))

theorem perturbed_complement_norm_gap (hAp : A.IsPositive)
    (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric)
    (f : H) (hf : inner ℂ (D.vector E hE) f = 0) :
    ‖(A + E) f‖ ≤ ((D.eigenvalue E hE).re - d / 2) * ‖f‖ := by
  apply (D.perturbed_complement_norm hAp E hE hEs f hf).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  have h := D.eigenvalue_error E hE
  rw [← D.eigenvalue_real E hE hEs, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h
  linarith [(abs_le.mp h).1, D.gap_pos]

theorem perturbed_residual_gap (hAp : A.IsPositive)
    (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric)
    (f : H) (hf : inner ℂ (D.vector E hE) f = 0) :
    (d / 2) * ‖f‖ ≤ ‖(A + E) f - D.eigenvalue E hE • f‖ := by
  have h := D.perturbed_complement_norm_gap hAp E hE hEs f hf
  have ht := norm_le_norm_sub_add (D.eigenvalue E hE • f) ((A + E) f)
  rw [norm_smul, ← D.eigenvalue_real E hE hEs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (D.eigenvalue_pos E hE hEs).le, norm_sub_rev] at ht
  rw [D.eigenvalue_real E hE hEs] at ht
  linarith

theorem perturbedData (hAp : A.IsPositive)
    (E : H →L[ℂ] H) (hE : ‖E‖ ≤ d / 64) (hEs : E.IsSymmetric) :
    Data (A + E) (D.vector E hE) (D.eigenvalue E hE).re (d / 2) where
  unit_norm := D.vector_norm E hE
  symmetric := D.symmetric.add hEs
  eigenvector := by rw [D.eigenvalue_real E hE hEs]; exact D.vector_eigen E hE
  gap_pos := by linarith [D.gap_pos]
  gap_le_mu := by
    have h := D.eigenvalue_error E hE
    rw [← D.eigenvalue_real E hE hEs, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    linarith [(abs_le.mp h).1, D.gap_pos, D.gap_le_mu]
  complement := D.perturbed_complement_norm_gap hAp E hE hEs

end Maxwell.Continuum.TopEigenPerturbation.Data
