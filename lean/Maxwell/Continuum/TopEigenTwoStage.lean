import Maxwell.Continuum.TopEigenDataTransport

/-! Two bounded perturbations with exact Gram spectral transport between
them. Neither the Gram operator nor the final operator is assumed compact. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.TopEigenPerturbation.TwoStage

open scoped InnerProduct

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
variable {A : X →L[ℂ] X} {u : X} {mu d : ℝ} (D : Data A u mu d)

def gramError (B : X →L[ℂ] Y) : X →L[ℂ] X := (B†).comp B - A

include D in
theorem gramError_symmetric (B : X →L[ℂ] Y) : (gramError (A := A) B).IsSymmetric :=
  (ContinuousLinearMap.isPositive_adjoint_comp_self B).isSelfAdjoint.isSymmetric.sub D.symmetric

def gramValue (B : X →L[ℂ] Y) (hb : ‖gramError (A := A) B‖ ≤ d / 64) : ℝ :=
  (D.eigenvalue (gramError B) hb).re

def gramVector (B : X →L[ℂ] Y) (hb : ‖gramError (A := A) B‖ ≤ d / 64) : X :=
  D.vector (gramError B) hb

theorem gramData (hA : A.IsPositive) (B : X →L[ℂ] Y)
    (hb : ‖gramError (A := A) B‖ ≤ d / 64) :
    Data ((B†).comp B) (gramVector D B hb) (gramValue D B hb) (d / 2) := by
  have he : A + gramError (A := A) B = (B†).comp B := by unfold gramError; abel
  exact he ▸ D.perturbedData hA (gramError B) hb (gramError_symmetric D B)

def fieldVector (B : X →L[ℂ] Y) (hb : ‖gramError (A := A) B‖ ≤ d / 64) : Y :=
  GramSpectral.vector (B†) (gramValue D B hb) (gramVector D B hb)

theorem fieldData (hA : A.IsPositive) (B : X →L[ℂ] Y)
    (hb : ‖gramError (A := A) B‖ ≤ d / 64) :
    Data (B.comp (B†)) (fieldVector D B hb) (gramValue D B hb) (d / 2) := by
  have hd : Data ((B†).comp (B††)) (gramVector D B hb) (gramValue D B hb) (d / 2) := by
    rw [ContinuousLinearMap.adjoint_adjoint]
    exact gramData D hA B hb
  simpa only [ContinuousLinearMap.adjoint_adjoint, fieldVector] using hd.gramData (B†)

def fieldError (B : X →L[ℂ] Y) (S : Y →L[ℂ] Y) : Y →L[ℂ] Y := S - B.comp (B†)

theorem fieldError_symmetric (B : X →L[ℂ] Y) (S : Y →L[ℂ] Y) (hS : S.IsSymmetric) :
    (fieldError B S).IsSymmetric :=
  hS.sub (ContinuousLinearMap.isPositive_self_comp_adjoint B).isSelfAdjoint.isSymmetric

def finalValue (hA : A.IsPositive) (B : X →L[ℂ] Y)
    (hb : ‖gramError (A := A) B‖ ≤ d / 64) (S : Y →L[ℂ] Y)
    (hs : ‖fieldError B S‖ ≤ (d / 2) / 64) : ℝ :=
  ((fieldData D hA B hb).eigenvalue (fieldError B S) hs).re

def finalVector (hA : A.IsPositive) (B : X →L[ℂ] Y)
    (hb : ‖gramError (A := A) B‖ ≤ d / 64) (S : Y →L[ℂ] Y)
    (hs : ‖fieldError B S‖ ≤ (d / 2) / 64) : Y :=
  (fieldData D hA B hb).vector (fieldError B S) hs

theorem finalData (hA : A.IsPositive) (B : X →L[ℂ] Y)
    (hb : ‖gramError (A := A) B‖ ≤ d / 64) (S : Y →L[ℂ] Y)
    (hS : S.IsSymmetric) (hs : ‖fieldError B S‖ ≤ (d / 2) / 64) :
    Data S (finalVector D hA B hb S hs) (finalValue D hA B hb S hs) (d / 4) := by
  have he : B.comp (B†) + fieldError B S = S := by unfold fieldError; abel
  have hd := (fieldData D hA B hb).perturbedData
    (ContinuousLinearMap.isPositive_self_comp_adjoint B) (fieldError B S) hs
    (fieldError_symmetric B S hS)
  rw [he] at hd
  simpa only [finalVector, finalValue, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hd

theorem gramValue_error (B : X →L[ℂ] Y) (hb : ‖gramError (A := A) B‖ ≤ d / 64) :
    |gramValue D B hb - mu| ≤ 4 * ‖gramError (A := A) B‖ := by
  have he := D.eigenvalue_error (gramError B) hb
  rw [← D.eigenvalue_real (gramError B) hb (gramError_symmetric D B),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he
  exact he

theorem finalValue_error (hA : A.IsPositive) (B : X →L[ℂ] Y)
    (hb : ‖gramError (A := A) B‖ ≤ d / 64) (S : Y →L[ℂ] Y)
    (hS : S.IsSymmetric) (hs : ‖fieldError B S‖ ≤ (d / 2) / 64) :
    |finalValue D hA B hb S hs - mu| ≤
      4 * ‖gramError (A := A) B‖ + 4 * ‖fieldError B S‖ := by
  have he := (fieldData D hA B hb).eigenvalue_error (fieldError B S) hs
  rw [← (fieldData D hA B hb).eigenvalue_real (fieldError B S) hs
      (fieldError_symmetric B S hS), ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at he
  change |finalValue D hA B hb S hs - gramValue D B hb| ≤ _ at he
  have ht := abs_sub_le (finalValue D hA B hb S hs) (gramValue D B hb) mu
  linarith [gramValue_error D B hb]

theorem finalVector_error (hA : A.IsPositive) (B : X →L[ℂ] Y)
    (hb : ‖gramError (A := A) B‖ ≤ d / 64) (S : Y →L[ℂ] Y)
    (hs : ‖fieldError B S‖ ≤ (d / 2) / 64) :
    ‖finalVector D hA B hb S hs - fieldVector D B hb‖ ≤ 8 * ‖fieldError B S‖ / d := by
  have he := (fieldData D hA B hb).vector_error (fieldError B S) hs
  change ‖finalVector D hA B hb S hs - fieldVector D B hb‖ ≤ _ at he
  convert he using 1
  ring

end Maxwell.Continuum.TopEigenPerturbation.TwoStage
