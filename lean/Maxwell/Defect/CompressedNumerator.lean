import Maxwell.Defect.RankOneResidual
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-! The pole numerator is obtained by compressing the actual analytic
spectral projector. Its rank-one center value is an operator identity. -/
namespace Maxwell.Defect

open InnerProductSpace

variable {U H W : Type*}
variable [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Compression by a finite source map, as an actual bounded linear map
on the space of ambient operators. -/
noncomputable def sourceCompression (F : U →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (U →L[ℂ] U) :=
  (ContinuousLinearMap.compL ℂ U H U (ContinuousLinearMap.adjoint F)).comp
    ((ContinuousLinearMap.compL ℂ U H H).flip F)

@[simp] theorem sourceCompression_apply (F : U →L[ℂ] H) (T : H →L[ℂ] H) :
    sourceCompression F T = (ContinuousLinearMap.adjoint F).comp (T.comp F) := rfl

/-- Compressing the actual rank-one projector gives the rank-one source
vector appearing in the edge singularity. -/
theorem sourceCompression_rankOne (F : U →L[ℂ] H) (φ : H) :
    sourceCompression F (rankOne ℂ φ φ) =
      rankOne ℂ (ContinuousLinearMap.adjoint F φ) (ContinuousLinearMap.adjoint F φ) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [rankOne_apply, ContinuousLinearMap.adjoint_inner_left]

/-- Exact pole extraction commutes with compression because compression
is a bounded linear map, with no assumption about numerator asymptotics. -/
theorem sourceCompression_pole_decomposition (F : U →L[ℂ] H)
    (inverse P regular : H →L[ℂ] H) (lam z : ℂ)
    (hpole : inverse = (lam - z)⁻¹ • P + regular) :
    sourceCompression F inverse = (lam - z)⁻¹ • sourceCompression F P +
      sourceCompression F regular := by
  rw [hpole, map_add, map_smul]

theorem sourceCompression_rankOne_pole (F : U →L[ℂ] H) (φ : H)
    (inverse regular : H →L[ℂ] H) (lam z : ℂ)
    (hpole : inverse = (lam - z)⁻¹ • rankOne ℂ φ φ + regular) :
    sourceCompression F inverse = (lam - z)⁻¹ •
      rankOne ℂ (ContinuousLinearMap.adjoint F φ) (ContinuousLinearMap.adjoint F φ) +
      sourceCompression F regular := by
  rw [sourceCompression_pole_decomposition F inverse _ regular lam z hpole,
    sourceCompression_rankOne]

/-- The left and right Fourier continuations are kept separate: each is
holomorphic, and at the real center they are the source adjoint and source. -/
noncomputable def compressedNumerator
    (sourceLeft : W → H →L[ℂ] U) (P : W → H →L[ℂ] H)
    (sourceRight : W → U →L[ℂ] H) (q : W) : U →L[ℂ] U :=
  (sourceLeft q).comp ((P q).comp (sourceRight q))

theorem analyticAt_operator_composition
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : W → F →L[ℂ] G) (B : W → E →L[ℂ] F) (q : W)
    (hA : AnalyticAt ℂ A q) (hB : AnalyticAt ℂ B q) :
    AnalyticAt ℂ (fun z => (A z).comp (B z)) q :=
  ((ContinuousLinearMap.compL ℂ E F G).analyticAt_bilinear _).comp₂ hA hB

omit [CompleteSpace U] [CompleteSpace H] in
/-- Analyticity follows from the actual projector and source families by
bounded bilinear composition. -/
theorem compressedNumerator_analyticAt
    (sourceLeft : W → H →L[ℂ] U) (P : W → H →L[ℂ] H)
    (sourceRight : W → U →L[ℂ] H) (q : W)
    (hL : AnalyticAt ℂ sourceLeft q) (hP : AnalyticAt ℂ P q)
    (hR : AnalyticAt ℂ sourceRight q) :
    AnalyticAt ℂ (compressedNumerator sourceLeft P sourceRight) q :=
  analyticAt_operator_composition sourceLeft (fun z => (P z).comp (sourceRight z)) q hL
    (analyticAt_operator_composition P sourceRight q hP hR)

omit [NormedAddCommGroup W] [NormedSpace ℂ W] in
/-- The analytic numerator's center value is the actual projected source
outer product, derived from the spectral projector's center identity. -/
theorem compressedNumerator_center
    (sourceLeft : W → H →L[ℂ] U) (P : W → H →L[ℂ] H)
    (sourceRight : W → U →L[ℂ] H) (q : W) (F : U →L[ℂ] H) (φ : H)
    (hL : sourceLeft q = ContinuousLinearMap.adjoint F)
    (hP : P q = rankOne ℂ φ φ) (hR : sourceRight q = F) :
    compressedNumerator sourceLeft P sourceRight q =
      rankOne ℂ (ContinuousLinearMap.adjoint F φ) (ContinuousLinearMap.adjoint F φ) := by
  rw [compressedNumerator, hL, hP, hR]
  exact sourceCompression_rankOne F φ

omit [CompleteSpace U] [CompleteSpace H] [NormedAddCommGroup W] [NormedSpace ℂ W] in
/-- The pole identity also holds pointwise for the varying analytic source
maps, producing precisely the analytic compressed numerator above. -/
theorem compressedNumerator_pole_decomposition
    (sourceLeft : W → H →L[ℂ] U) (P regular inverse : W → H →L[ℂ] H)
    (sourceRight : W → U →L[ℂ] H) (lam : W → ℂ) (z : ℂ) (q : W)
    (hpole : inverse q = (lam q - z)⁻¹ • P q + regular q) :
    compressedNumerator sourceLeft inverse sourceRight q =
      (lam q - z)⁻¹ • compressedNumerator sourceLeft P sourceRight q +
        compressedNumerator sourceLeft regular sourceRight q := by
  apply ContinuousLinearMap.ext
  intro x
  simp [compressedNumerator, hpole]

end Maxwell.Defect
