import Maxwell.Continuum.CoerciveInverse

/-! Orthogonal material compressions inherit the physical energy bounds. -/

noncomputable section

namespace Maxwell.Continuum.Compression

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (K : Submodule ℂ H) [CompleteSpace K]

def compress (B : H →L[ℂ] H) : K →L[ℂ] K :=
  K.orthogonalProjectionOnto.comp (B.comp K.subtypeL)

omit [CompleteSpace H] in
theorem inner_compress (B : H →L[ℂ] H) (x y : K) :
    inner ℂ x (compress K B y) = inner ℂ (x : H) (B y) := by
  exact K.inner_orthogonalProjectionOnto_eq_of_mem_left x (B y)

omit [CompleteSpace H] in
theorem compress_symmetric (B : H →L[ℂ] H) (hB : B.IsSymmetric) :
    (compress K B).IsSymmetric := by
  intro x y
  change inner ℂ (K.orthogonalProjectionOnto (B x)) y =
    inner ℂ x (K.orthogonalProjectionOnto (B y))
  rw [K.inner_orthogonalProjectionOnto_eq_of_mem_right,
    K.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hB x.val y.val

omit [CompleteSpace H] in
theorem compress_norm_le (B : H →L[ℂ] H) : ‖compress K B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (K.norm_orthogonalProjectionOnto_apply_le (B x)).trans (B.le_opNorm x.val)

omit [CompleteSpace H] in
theorem compress_coercive (B : H →L[ℂ] H) {c : ℝ}
    (hB : CoerciveInverse.Coercive B c) : CoerciveInverse.Coercive (compress K B) c := by
  intro x
  rw [inner_compress]
  exact hB x.val

omit [CompleteSpace H] in
theorem compress_upper (B : H →L[ℂ] H) {c : ℝ}
    (hB : ∀ x, (inner ℂ x (B x)).re ≤ c * ‖x‖ ^ 2) (x : K) :
    (inner ℂ x (compress K B x)).re ≤ c * ‖x‖ ^ 2 := by
  rw [inner_compress]
  exact hB x.val

def offDiagonal (B : H →L[ℂ] H) : Kᗮ →L[ℂ] K :=
  K.orthogonalProjectionOnto.comp (B.comp Kᗮ.subtypeL)

omit [CompleteSpace H] in
theorem offDiagonal_norm_le (B : H →L[ℂ] H) : ‖offDiagonal K B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (K.norm_orthogonalProjectionOnto_apply_le (B x)).trans (B.le_opNorm x.val)

theorem offDiagonal_adjoint (B : H →L[ℂ] H) (hB : B.IsSymmetric) (x : K) :
    (offDiagonal K B).adjoint x = Kᗮ.orthogonalProjectionOnto (B x) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right,
    Kᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left]
  change inner ℂ (K.orthogonalProjectionOnto (B y)) x = inner ℂ (y : H) (B x)
  rw [K.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact hB y.val x.val

end Maxwell.Continuum.Compression
