import Maxwell.Composition.SourceIdentity
import Maxwell.Composition.Residual
import Maxwell.Composition.Mediator
import Maxwell.Readout
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Physical residual multiplier and every-output recovery

This module combines the exact weighted source identity with quantitative
operator estimates.  The field variable is arbitrary throughout.  The local
complementary spectral separation, interaction error, and logical Schur
identity remain explicit premises until supplied by the corresponding
construction modules.
-/

namespace Maxwell.Composition

section PhysicalMultiplier

variable {E D B C : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]

def physicalResidualMap (K : E ≃L[ℝ] E) (W : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (M : D →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C) : E →L[ℝ] B :=
  (complementaryResidualMap M Z P R Dc).comp
    ((W : D →L[ℝ] D).comp (Q.comp (K.symm : E →L[ℝ] E)))

theorem complementary_residual_map_norm_le_two
    (M : D →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hmix : ‖(P.comp (M.comp Z)).comp (Dc.symm : C →L[ℝ] C)‖ ≤ 1) :
    ‖complementaryResidualMap M Z P R Dc‖ ≤ 2 := by
  have hcorrection : ‖((P.comp (M.comp Z)).comp
      (Dc.symm : C →L[ℝ] C)).comp R‖ ≤ 1 := by
    calc
      _ ≤ ‖(P.comp (M.comp Z)).comp (Dc.symm : C →L[ℝ] C)‖ * ‖R‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hmix hR (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [complementaryResidualMap, ← ContinuousLinearMap.comp_assoc]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The full residual map has norm at most 2 L_b, independently of the
number of occupied defect blocks. -/
theorem physical_residual_map_norm_le
    (K : E ≃L[ℝ] E) (W : D ≃L[ℝ] D) (Q : E →L[ℝ] D)
    (M : D →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C) (L : ℝ)
    (hK : ‖(K.symm : E →L[ℝ] E)‖ ≤ L)
    (hW : ‖(W : D →L[ℝ] D)‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hmix : ‖(P.comp (M.comp Z)).comp (Dc.symm : C →L[ℝ] C)‖ ≤ 1) :
    ‖physicalResidualMap K W Q M Z P R Dc‖ ≤ 2 * L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hK
  have hQK : ‖Q.comp (K.symm : E →L[ℝ] E)‖ ≤ L := by
    calc
      _ ≤ ‖Q‖ * ‖(K.symm : E →L[ℝ] E)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * L := mul_le_mul hQ hK (norm_nonneg _) zero_le_one
      _ = L := one_mul L
  have hWQK : ‖(W : D →L[ℝ] D).comp (Q.comp (K.symm : E →L[ℝ] E))‖ ≤ L := by
    calc
      _ ≤ ‖(W : D →L[ℝ] D)‖ * ‖Q.comp (K.symm : E →L[ℝ] E)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * L := mul_le_mul hW hQK (norm_nonneg _) zero_le_one
      _ = L := one_mul L
  unfold physicalResidualMap
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (complementary_residual_map_norm_le_two M Z P R Dc hP hR hmix)
      hWQK (norm_nonneg _) (by norm_num))

/-- The actual emitted source, arbitrary solver residual, and exact
weighted physical readout yield the stated bright residual budget. -/
theorem physical_bright_residual_budget
    (K : E ≃L[ℝ] E) (V W : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E)
    (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C)
    (hQQt : ∀ d, Q (Qt d) = d)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (weightedBirmanSchwinger K V W Q Qt (Z c)) = Dc c)
    (hPU : ∀ b, P (U b) = b) (hRU : ∀ b, R (U b) = 0)
    (α ε G J cW L : ℝ) (hε : 0 ≤ ε)
    (hJ : 0 < J) (hcW : 0 < cW) (hL : 0 < L)
    (hK : ‖(K.symm : E →L[ℝ] E)‖ ≤ L)
    (hW : ‖(W : D →L[ℝ] D)‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hmix : ‖(P.comp ((weightedBirmanSchwinger K V W Q Qt).comp Z)).comp
      (Dc.symm : C →L[ℝ] C)‖ ≤ 1)
    (g : B) (y fhat : E)
    (hsourceNorm : ‖fhat‖ ≤ 2 * α * J * cW * G)
    (hsourceError : ‖fhat - localIdealSource K W Qt (U (α • g))‖ ≤
      α * ε * G / (8192 * L))
    (hsolver : ‖finitePhysicalOperator K V Q Qt y - fhat‖ ≤
      (ε / (8192 * J * cW * L)) * ‖fhat‖) :
    ‖brightSchurOperator (weightedBirmanSchwinger K V W Q Qt) U Z P R Dc
      (P (weightedDefectCoordinates V W Q y)) - α • g‖ ≤
        3 * α * ε * G / 4096 := by
  rw [physical_bright_residual_identity K V W Q Qt U Z P R Dc
    hQQt hdecomp hDc hPU hRU (α • g) y]
  have hres := physical_residual_budget (finitePhysicalOperator K V Q Qt)
    y fhat (localIdealSource K W Qt (U (α • g))) α ε G J cW L
    hε hJ hcW hL hsourceNorm hsourceError hsolver
  exact bright_residual_budget
    (physicalResidualMap K W Q (weightedBirmanSchwinger K V W Q Qt) Z P R Dc)
    (finitePhysicalOperator K V Q Qt y - localIdealSource K W Qt (U (α • g)))
    α ε G L hL
    (physical_residual_map_norm_le K W Q (weightedBirmanSchwinger K V W Q Qt)
      Z P R Dc L hK hW hQ hP hR hmix) hres

end PhysicalMultiplier

section FinalLogicalRecovery

variable {D B C : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- Once the physical bright residual has been proved, the actual target
perturbation and mediator identities imply the ideal terminal residual.
No residual coordinate is set to zero. -/
theorem ideal_logical_residual_budget
    (S : D ≃L[ℝ] D) (T : D →L[ℝ] D)
    (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dm : C ≃L[ℝ] C)
    (Γ : B →L[ℝ] B)
    (α ε G K : ℝ) (hα : 0 < α) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hG : 0 ≤ G) (hK : 0 < K)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDm : ∀ c, R (T (Z c)) = Dm c)
    (hPU : ∀ b, P (U b) = b) (hRU : ∀ b, R (U b) = 0)
    (hSchur : brightSchurOperator T U Z P R Dm = α • Γ)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hmix : ‖(P.comp (T.comp Z)).comp (Dm.symm : C →L[ℝ] C)‖ ≤ 3)
    (hInv : ‖(S.symm : D →L[ℝ] D)‖ ≤ 32 * K / α)
    (hpert : ‖(S : D →L[ℝ] D) - T‖ ≤ α * ε / (4096 * K))
    (z : D) (g : B) (hg : ‖U g‖ ≤ G)
    (hres : ‖S z - α • U g‖ ≤ 3 * α * ε * G / 4096) :
    ‖Γ (P z) - g‖ ≤ ε * G / 16 := by
  have hz := bright_amplitude_budget S z (U g) α ε G K hα hεhalf hG hK.le hg hInv hres
  have htarget := target_residual_budget (S : D →L[ℝ] D) T z (α • U g)
    α ε G K hK hres hpert hz
  have hterminal := mediator_residual_transfer T U Z P R Dm Γ α hα
    hdecomp hDm hPU hRU hSchur hP hR hmix z g
  have hbound : ‖Γ (P z) - g‖ ≤ 9 * ε * G / 256 := by
    calc
      _ ≤ (4 / α) * ‖T z - α • U g‖ := hterminal
      _ ≤ (4 / α) * (36 * α * ε * G / 4096) :=
        mul_le_mul_of_nonneg_left htarget (by positivity)
      _ = 9 * ε * G / 256 := by field_simp; ring
  have hεG : 0 ≤ ε * G := mul_nonneg hε hG
  nlinarith

end FinalLogicalRecovery

section ActualFiniteMessages

/-- The actual stored rational weighted readout, evaluated on every
accurate fixed-width message, satisfies the logical residual budget.
The calibration premise compares that stored readout with the physical
mode readout. It cannot silently replace the emitted coefficients by
ideal eigenmode coefficients. -/
theorem finite_weighted_recovery_budget {ι : Type*} {n : ℕ}
    (D : Target.WeightedDecoder ι n) (w : D.Messages) (y : ι → ℝ)
    (hw : D.Accurate w y)
    (Γ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (z g : EuclideanSpace ℝ (Fin n)) (ε G W : ℝ)
    (hres : ‖Γ z - g‖ ≤ ε * G / 16) (hΓ : ‖Γ‖ ≤ 7)
    (hcal : ‖WithLp.toLp 2 (D.ideal y) - z‖ ≤ 3 * ε * G / 1024)
    (hW : 0 ≤ W)
    (hrow : ∀ i, ∑ j ∈ D.support i, |(D.weight i j : ℝ)| ≤ W)
    (hprecision : Real.sqrt n * (W / (2 : ℝ) ^ D.format.fractionalBits) ≤
      ε * G / 128) :
    ‖Γ (WithLp.toLp 2 (fun i => (D.decode w i : ℝ))) - g‖ ≤
      141 * ε * G / 1024 := by
  let zhat : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 fun i => (D.decode w i : ℝ)
  let zcal : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (D.ideal y)
  have haccess : ‖zhat - zcal‖ ≤ ε * G / 128 := by
    exact (D.decode_euclidean_error_le w y hw W hW hrow).trans hprecision
  have hread : ‖zhat - z‖ ≤ 11 * ε * G / 1024 := by
    calc
      ‖zhat - z‖ = ‖(zhat - zcal) + (zcal - z)‖ := by congr 1; abel
      _ ≤ ‖zhat - zcal‖ + ‖zcal - z‖ := norm_add_le _ _
      _ ≤ ε * G / 128 + 3 * ε * G / 1024 := add_le_add haccess hcal
      _ = 11 * ε * G / 1024 := by ring
  exact computed_logical_residual_budget Γ z zhat g ε G hres hΓ hread

theorem finite_weighted_recovery_below_half {ι : Type*} {n : ℕ}
    (D : Target.WeightedDecoder ι n) (w : D.Messages) (y : ι → ℝ)
    (hw : D.Accurate w y)
    (Γ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (z g : EuclideanSpace ℝ (Fin n)) (ε G W : ℝ) (hεG : 0 < ε * G)
    (hres : ‖Γ z - g‖ ≤ ε * G / 16) (hΓ : ‖Γ‖ ≤ 7)
    (hcal : ‖WithLp.toLp 2 (D.ideal y) - z‖ ≤ 3 * ε * G / 1024)
    (hW : 0 ≤ W)
    (hrow : ∀ i, ∑ j ∈ D.support i, |(D.weight i j : ℝ)| ≤ W)
    (hprecision : Real.sqrt n * (W / (2 : ℝ) ^ D.format.fractionalBits) ≤
      ε * G / 128) :
    ‖Γ (WithLp.toLp 2 (fun i => (D.decode w i : ℝ))) - g‖ < ε * G / 2 := by
  have h := finite_weighted_recovery_budget D w y hw Γ z g ε G W
    hres hΓ hcal hW hrow hprecision
  nlinarith

end ActualFiniteMessages

end Maxwell.Composition
