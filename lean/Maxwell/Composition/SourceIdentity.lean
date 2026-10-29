import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Abel

/-!
# Exact weighted source and readout identities

The maps below use the actual finite background inverse.  The weighting and
defect strength are invertible local coordinate changes; the full physical
operator is not assumed invertible.  The two identities are valid for every
physical vector and every residual, including auxiliary residuals.
-/

namespace Maxwell.Composition

section WeightedSource

variable {E D : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Finite background minus the actual defect perturbation. -/
def finitePhysicalOperator (K : E ≃L[ℝ] E) (V : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E) : E →L[ℝ] E :=
  (K : E →L[ℝ] E) - Qt.comp ((V : D →L[ℝ] D).comp Q)

/-- The weighted finite Birman--Schwinger matrix as a bounded operator. -/
def weightedBirmanSchwinger (K : E ≃L[ℝ] E) (V W : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E) : D →L[ℝ] D :=
  (W : D →L[ℝ] D).comp
    (((V.symm : D →L[ℝ] D) - Q.comp ((K.symm : E →L[ℝ] E).comp Qt)).comp
      (W : D →L[ℝ] D))

def weightedDefectCoordinates (V W : D ≃L[ℝ] D) (Q : E →L[ℝ] D)
    (y : E) : D := W.symm (V (Q y))

/-- The local ideal source is one application of the finite background to
a defect-supported injection. It is not a background solve. -/
def localIdealSource (K : E ≃L[ℝ] E) (W : D ≃L[ℝ] D)
    (Qt : D →L[ℝ] E) (u : D) : E := K (Qt (W.symm u))

theorem weighted_birman_schwinger_action
    (K : E ≃L[ℝ] E) (V W : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E) (y : E) :
    weightedBirmanSchwinger K V W Q Qt (weightedDefectCoordinates V W Q y) =
      W (Q (K.symm (finitePhysicalOperator K V Q Qt y))) := by
  simp [weightedBirmanSchwinger, weightedDefectCoordinates,
    finitePhysicalOperator, map_sub]

/-- Restriction followed by injection is the identity on the complete
defect coordinate space, not a per-defect error estimate. -/
theorem local_source_injection_identity
    (K : E ≃L[ℝ] E) (W : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E)
    (hQ : ∀ d, Q (Qt d) = d) (u : D) :
    W (Q (K.symm (localIdealSource K W Qt u))) = u := by
  simp [localIdealSource, hQ]

/-- The exact identity starts from the field and the source actually used
in the residual. No particular approximate solution is selected. -/
theorem weighted_birman_schwinger_residual
    (K : E ≃L[ℝ] E) (V W : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E)
    (hQ : ∀ d, Q (Qt d) = d) (u : D) (y : E) :
    weightedBirmanSchwinger K V W Q Qt (weightedDefectCoordinates V W Q y) =
      u + W (Q (K.symm
        (finitePhysicalOperator K V Q Qt y - localIdealSource K W Qt u))) := by
  rw [weighted_birman_schwinger_action]
  simp only [map_sub]
  rw [local_source_injection_identity K W Q Qt hQ u]
  abel

end WeightedSource

section ComplementaryElimination

variable {D B C : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]

def brightSchurOperator (M : D →L[ℝ] D) (U : B →L[ℝ] D)
    (Z : C →L[ℝ] D) (P : D →L[ℝ] B) (R : D →L[ℝ] C)
    (Dc : C ≃L[ℝ] C) : B →L[ℝ] B :=
  P.comp (M.comp U) -
    (P.comp (M.comp Z)).comp
      ((Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U)))

def complementaryResidualMap (M : D →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C) : D →L[ℝ] B :=
  P - (P.comp (M.comp Z)).comp ((Dc.symm : C →L[ℝ] C).comp R)

/-- Exact elimination retains an arbitrary error in the complementary
equations. The decomposition is an algebraic direct-sum identity; norm
control is supplied separately by the orthogonal-mode construction. -/
theorem complementary_schur_action
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (M (Z c)) = Dc c) (w : D) :
    brightSchurOperator M U Z P R Dc (P w) =
      complementaryResidualMap M Z P R Dc (M w) := by
  have hMw : M w = M (U (P w)) + M (Z (R w)) := by
    rw [← map_add, ← hdecomp w]
  simp only [brightSchurOperator, complementaryResidualMap,
    sub_apply, ContinuousLinearMap.comp_apply]
  rw [hMw]
  simp only [map_add, hDc, ContinuousLinearEquiv.coe_apply, Dc.symm_apply_apply]
  abel

/-- With a bright-only source, complementary elimination yields the exact
residual-transfer identity consumed by the norm estimates. -/
theorem complementary_schur_residual
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (M (Z c)) = Dc c)
    (hPU : ∀ b, P (U b) = b) (hRU : ∀ b, R (U b) = 0)
    (w : D) (g : B) (r : D) (hMw : M w = U g + r) :
    brightSchurOperator M U Z P R Dc (P w) =
      g + complementaryResidualMap M Z P R Dc r := by
  rw [complementary_schur_action M U Z P R Dc hdecomp hDc w, hMw, map_add]
  congr 1
  simp [complementaryResidualMap, hPU, hRU]

end ComplementaryElimination

section PhysicalBrightIdentity

variable {E D B C : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- The complete exact source/readout identity used in the paper. Its
right-hand side is the arbitrary residual for the actual finite operator.
All inverse assumptions concern the background or the complementary block;
invertibility of the full physical operator is not assumed. -/
theorem physical_bright_residual_identity
    (K : E ≃L[ℝ] E) (V W : D ≃L[ℝ] D)
    (Q : E →L[ℝ] D) (Qt : D →L[ℝ] E)
    (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C)
    (hQ : ∀ d, Q (Qt d) = d)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (weightedBirmanSchwinger K V W Q Qt (Z c)) = Dc c)
    (hPU : ∀ b, P (U b) = b) (hRU : ∀ b, R (U b) = 0)
    (g : B) (y : E) :
    brightSchurOperator (weightedBirmanSchwinger K V W Q Qt) U Z P R Dc
        (P (weightedDefectCoordinates V W Q y)) - g =
      complementaryResidualMap (weightedBirmanSchwinger K V W Q Qt) Z P R Dc
        (W (Q (K.symm
          (finitePhysicalOperator K V Q Qt y - localIdealSource K W Qt (U g))))) := by
  have hweighted := weighted_birman_schwinger_residual K V W Q Qt hQ (U g) y
  have h := complementary_schur_residual
    (weightedBirmanSchwinger K V W Q Qt) U Z P R Dc hdecomp hDc hPU hRU
    (weightedDefectCoordinates V W Q y) g
    (W (Q (K.symm
      (finitePhysicalOperator K V Q Qt y - localIdealSource K W Qt (U g)))))
    hweighted
  rw [h]
  abel

end PhysicalBrightIdentity

end Maxwell.Composition
