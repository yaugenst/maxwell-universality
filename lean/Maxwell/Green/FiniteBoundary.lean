import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Finite/infinite resolvent identities on the full defect union. The maps
use the original Hilbert-space norms; no count of selected coordinates is
introduced. The concrete PEC restriction instantiates these identities. -/

namespace Maxwell.Green

variable {𝕜 E F D : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup D] [NormedSpace 𝕜 D]

def boundaryMismatch (K : F →L[𝕜] F) (P : E →L[𝕜] F)
    (H : E →L[𝕜] E) : E →L[𝕜] F := K.comp P - P.comp H

/-- Identical scalar detuning cancels from the boundary mismatch. -/
theorem boundaryMismatch_shift (K : F →L[𝕜] F) (P : E →L[𝕜] F)
    (H : E →L[𝕜] E) (σ : 𝕜) :
    boundaryMismatch (K - σ • ContinuousLinearMap.id 𝕜 F) P
      (H - σ • ContinuousLinearMap.id 𝕜 E) = boundaryMismatch K P H := by
  ext x
  simp only [boundaryMismatch, ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul]
  abel

/-- Exact restriction identity, with full finite and infinite inverses. -/
theorem restriction_resolvent_identity (K : F ≃L[𝕜] F) (H : E ≃L[𝕜] E)
    (P : E →L[𝕜] F) :
    (K.symm : F →L[𝕜] F).comp P - P.comp (H.symm : E →L[𝕜] E) =
      -((K.symm : F →L[𝕜] F).comp
        ((boundaryMismatch K P H).comp (H.symm : E →L[𝕜] E))) := by
  ext x
  simp only [boundaryMismatch, ContinuousLinearMap.comp_apply, sub_apply,
    neg_apply, ContinuousLinearEquiv.coe_coe, map_sub,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  abel

/-- Compression onto an arbitrary entire union of defect coordinates.
The input and output selection maps are used only through their norms. -/
theorem compressed_restriction_identity (K : F ≃L[𝕜] F) (H : E ≃L[𝕜] E)
    (P : E →L[𝕜] F) (Q : F →L[𝕜] D) (B : D →L[𝕜] E) :
    Q.comp ((K.symm : F →L[𝕜] F).comp (P.comp B)) -
      (Q.comp P).comp ((H.symm : E →L[𝕜] E).comp B) =
      -(Q.comp ((K.symm : F →L[𝕜] F).comp
        ((boundaryMismatch K P H).comp ((H.symm : E →L[𝕜] E).comp B)))) := by
  ext x
  have h := congrArg (fun L : E →L[𝕜] F => Q (L (B x)))
    (restriction_resolvent_identity K H P)
  simpa only [ContinuousLinearMap.comp_apply, sub_apply,
    neg_apply, map_sub, map_neg] using h

/-- If the boundary mismatch sees only a strip, the infinite propagation
from the whole defect union to that strip is charged exactly once. -/
theorem compressed_boundary_error_le
    (K : F ≃L[𝕜] F) (H : E ≃L[𝕜] E)
    (P : E →L[𝕜] F) (Q : F →L[𝕜] D) (B : D →L[𝕜] E)
    (strip : E →L[𝕜] E)
    (hsupport : boundaryMismatch K P H = (boundaryMismatch K P H).comp strip)
    (L J ε : ℝ) (hQ : ‖Q‖ ≤ 1)
    (hK : ‖(K.symm : F →L[𝕜] F)‖ ≤ L)
    (hT : ‖boundaryMismatch K P H‖ ≤ J)
    (htail : ‖strip.comp ((H.symm : E →L[𝕜] E).comp B)‖ ≤ ε) :
    ‖Q.comp ((K.symm : F →L[𝕜] F).comp (P.comp B)) -
      (Q.comp P).comp ((H.symm : E →L[𝕜] E).comp B)‖ ≤ L * J * ε := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hK
  have hJ : 0 ≤ J := (norm_nonneg _).trans hT
  have hε : 0 ≤ ε := (norm_nonneg _).trans htail
  rw [compressed_restriction_identity, norm_neg]
  rw [hsupport, ContinuousLinearMap.comp_assoc]
  calc
    _ ≤ ‖Q‖ * ‖(K.symm : F →L[𝕜] F).comp
        ((boundaryMismatch K P H).comp (strip.comp ((H.symm : E →L[𝕜] E).comp B)))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Q‖ * (‖(K.symm : F →L[𝕜] F)‖ *
        ‖(boundaryMismatch K P H).comp (strip.comp ((H.symm : E →L[𝕜] E).comp B))‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Q‖ * (‖(K.symm : F →L[𝕜] F)‖ *
        (‖boundaryMismatch K P H‖ * ‖strip.comp ((H.symm : E →L[𝕜] E).comp B)‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (L * (J * ε)) := by gcongr
    _ = _ := by ring

/-- Difference of two genuine inverse operators. -/
theorem inverse_difference_identity (A B : E ≃L[𝕜] E) :
    (A.symm : E →L[𝕜] E) - (B.symm : E →L[𝕜] E) =
      (A.symm : E →L[𝕜] E).comp
        (((B : E →L[𝕜] E) - (A : E →L[𝕜] E)).comp (B.symm : E →L[𝕜] E)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearEquiv.coe_coe, map_sub,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem inverse_difference_norm_le (A B : E ≃L[𝕜] E) :
    ‖(A.symm : E →L[𝕜] E) - (B.symm : E →L[𝕜] E)‖ ≤
      ‖(A.symm : E →L[𝕜] E)‖ * ‖(B : E →L[𝕜] E) - (A : E →L[𝕜] E)‖ *
        ‖(B.symm : E →L[𝕜] E)‖ := by
  rw [inverse_difference_identity]
  calc
    _ ≤ ‖(A.symm : E →L[𝕜] E)‖ *
        ‖(((B : E →L[𝕜] E) - (A : E →L[𝕜] E)).comp (B.symm : E →L[𝕜] E))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(A.symm : E →L[𝕜] E)‖ *
        (‖(B : E →L[𝕜] E) - (A : E →L[𝕜] E)‖ * ‖(B.symm : E →L[𝕜] E)‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by ring

/-- Contractive coordinate selection never increases an operator error. -/
theorem compression_norm_le (Q : E →L[𝕜] D) (A : E →L[𝕜] E)
    (B : D →L[𝕜] E) (hQ : ‖Q‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖Q.comp (A.comp B)‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖Q‖ * ‖A.comp B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Q‖ * (‖A‖ * ‖B‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖A‖ * 1) := by gcongr
    _ = _ := by ring

/-- Scalar detuning changes an infinite inverse by its two inverse norms
times the scalar magnitude; the identity norm bound also covers zero spaces. -/
theorem scalar_shift_inverse_error (H R : E ≃L[𝕜] E) (σ : 𝕜)
    (hshift : (R : E →L[𝕜] E) =
      (H : E →L[𝕜] E) - σ • ContinuousLinearMap.id 𝕜 E) :
    ‖(R.symm : E →L[𝕜] E) - (H.symm : E →L[𝕜] E)‖ ≤
      ‖(R.symm : E →L[𝕜] E)‖ * ‖σ‖ * ‖(H.symm : E →L[𝕜] E)‖ := by
  have hsmall : ‖(H : E →L[𝕜] E) - (R : E →L[𝕜] E)‖ ≤ ‖σ‖ := by
    rw [hshift, sub_sub_cancel, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  exact (inverse_difference_norm_le R H).trans (by gcongr)

/-- The complete buffered-background error, compressed to the entire defect
union. The two summands are respectively bulk detuning and propagation to
the boundary strip, independent of the number of defects. -/
theorem finite_background_compression_error
    (K : F ≃L[𝕜] F) (H R : E ≃L[𝕜] E)
    (P : E →L[𝕜] F) (Q : F →L[𝕜] D) (B : D →L[𝕜] E)
    (strip : E →L[𝕜] E) (σ : 𝕜)
    (hshift : (R : E →L[𝕜] E) =
      (H : E →L[𝕜] E) - σ • ContinuousLinearMap.id 𝕜 E)
    (hsupport : boundaryMismatch K P R = (boundaryMismatch K P R).comp strip)
    (g τ J L μ buffer : ℝ) (hg : 0 < g) (hτ : ‖σ‖ ≤ τ)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hK : ‖(K.symm : F →L[𝕜] F)‖ ≤ L)
    (hH : ‖(H.symm : E →L[𝕜] E)‖ ≤ 1 / g)
    (hR : ‖(R.symm : E →L[𝕜] E)‖ ≤ 2 / g)
    (hT : ‖boundaryMismatch K P R‖ ≤ 2 * J)
    (htail : ‖strip.comp ((R.symm : E →L[𝕜] E).comp B)‖ ≤
      (2 / g) * Real.exp (-μ * buffer)) :
    ‖Q.comp ((K.symm : F →L[𝕜] F).comp (P.comp B)) -
      (Q.comp P).comp ((H.symm : E →L[𝕜] E).comp B)‖ ≤
      2 * τ / g ^ 2 + (4 * J * L / g) * Real.exp (-μ * buffer) := by
  have hτ0 : 0 ≤ τ := (norm_nonneg σ).trans hτ
  let A := Q.comp ((K.symm : F →L[𝕜] F).comp (P.comp B))
  let C := (Q.comp P).comp ((R.symm : E →L[𝕜] E).comp B)
  let D₀ := (Q.comp P).comp ((H.symm : E →L[𝕜] E).comp B)
  have hboundary : ‖A - C‖ ≤ L * (2 * J) * ((2 / g) * Real.exp (-μ * buffer)) :=
    compressed_boundary_error_le K R P Q B strip hsupport L (2 * J)
      ((2 / g) * Real.exp (-μ * buffer)) hQ hK hT htail
  have hQP : ‖Q.comp P‖ ≤ 1 := by
    calc
      _ ≤ ‖Q‖ * ‖P‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have hbulk : ‖C - D₀‖ ≤ 2 * τ / g ^ 2 := by
    have heq : C - D₀ = (Q.comp P).comp
        (((R.symm : E →L[𝕜] E) - (H.symm : E →L[𝕜] E)).comp B) := by
      ext x
      simp only [C, D₀, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    rw [heq]
    calc
      _ ≤ ‖(R.symm : E →L[𝕜] E) - (H.symm : E →L[𝕜] E)‖ :=
        compression_norm_le _ _ _ hQP hB
      _ ≤ ‖(R.symm : E →L[𝕜] E)‖ * ‖σ‖ * ‖(H.symm : E →L[𝕜] E)‖ :=
        scalar_shift_inverse_error H R σ hshift
      _ ≤ (2 / g) * τ * (1 / g) := by gcongr
      _ = _ := by ring
  change ‖A - D₀‖ ≤ _
  calc
    _ ≤ ‖A - C‖ + ‖C - D₀‖ := norm_sub_le_norm_sub_add_norm_sub A C D₀
    _ ≤ L * (2 * J) * ((2 / g) * Real.exp (-μ * buffer)) + 2 * τ / g ^ 2 :=
      add_le_add hboundary hbulk
    _ = _ := by ring

end Maxwell.Green
