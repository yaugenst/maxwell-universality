import Maxwell.Continuum.FiniteAuxiliaryNorms
import Maxwell.Composition.Complement

/-! Complex-linear block elimination on the full well direct sum.
The inverse identities reuse the dimension-free shared algebra after
restriction of scalars; the constructed inverse remains complex-linear. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

variable {E B C : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C]

def schurOperator (M : E →L[ℂ] E) (U : B →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C) : B →L[ℂ] B :=
  P.comp (M.comp U)-(P.comp (M.comp Z)).comp
    ((Dc.symm : C →L[ℂ] C).comp (R.comp (M.comp U)))

def schurResidual (M : E →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C) : E →L[ℂ] B :=
  P-(P.comp (M.comp Z)).comp ((Dc.symm : C →L[ℂ] C).comp R)

def schurLift (M : E →L[ℂ] E) (U : B →L[ℂ] E) (Z : C →L[ℂ] E)
    (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C) : B →L[ℂ] E :=
  U-Z.comp ((Dc.symm : C →L[ℂ] C).comp (R.comp (M.comp U)))

def schurFullInverse (M : E →L[ℂ] E) (U : B →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C) (S : B ≃L[ℂ] B) : E →L[ℂ] E :=
  (schurLift M U Z R Dc).comp ((S.symm : B →L[ℂ] B).comp (schurResidual M Z P R Dc))+
    Z.comp ((Dc.symm : C →L[ℂ] C).comp R)

theorem schurFullInverse_left (M : E →L[ℂ] E) (U : B →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C) (S : B ≃L[ℂ] B)
    (hdecomp : ∀ x, x = U (P x)+Z (R x))
    (hDc : ∀ c, R (M (Z c)) = Dc c)
    (hS : (S : B →L[ℂ] B) = schurOperator M U Z P R Dc) :
    (schurFullInverse M U Z P R Dc S).comp M = ContinuousLinearMap.id ℂ E := by
  have hSr : (S.restrictScalars ℝ : B →L[ℝ] B) = Composition.brightSchurOperator
      (M.restrictScalars ℝ) (U.restrictScalars ℝ) (Z.restrictScalars ℝ)
      (P.restrictScalars ℝ) (R.restrictScalars ℝ) (Dc.restrictScalars ℝ) := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun F : B →L[ℂ] B => F x) hS
  have he := Composition.complementaryInverse_comp
    (M.restrictScalars ℝ) (U.restrictScalars ℝ) (Z.restrictScalars ℝ)
    (P.restrictScalars ℝ) (R.restrictScalars ℝ) (Dc.restrictScalars ℝ) (S.restrictScalars ℝ)
    hdecomp hDc hSr
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun F : E →L[ℝ] E => F x) he

theorem schurFullInverse_right (M : E →L[ℂ] E) (U : B →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C) (S : B ≃L[ℂ] B)
    (hdecomp : ∀ x, x = U (P x)+Z (R x))
    (hDc : ∀ c, R (M (Z c)) = Dc c)
    (hS : (S : B →L[ℂ] B) = schurOperator M U Z P R Dc)
    (hPU : ∀ b, P (U b) = b) (hPZ : ∀ c, P (Z c) = 0)
    (hRU : ∀ b, R (U b) = 0) (hRZ : ∀ c, R (Z c) = c) :
    M.comp (schurFullInverse M U Z P R Dc S) = ContinuousLinearMap.id ℂ E := by
  have hSr : (S.restrictScalars ℝ : B →L[ℝ] B) = Composition.brightSchurOperator
      (M.restrictScalars ℝ) (U.restrictScalars ℝ) (Z.restrictScalars ℝ)
      (P.restrictScalars ℝ) (R.restrictScalars ℝ) (Dc.restrictScalars ℝ) := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun F : B →L[ℂ] B => F x) hS
  have he := Composition.comp_complementaryInverse
    (M.restrictScalars ℝ) (U.restrictScalars ℝ) (Z.restrictScalars ℝ)
    (P.restrictScalars ℝ) (R.restrictScalars ℝ) (Dc.restrictScalars ℝ) (S.restrictScalars ℝ)
    hdecomp hDc hSr hPU hPZ hRU hRZ
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun F : E →L[ℝ] E => F x) he

def schurFullEquiv (M : E →L[ℂ] E) (U : B →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C) (S : B ≃L[ℂ] B)
    (hdecomp : ∀ x, x = U (P x)+Z (R x))
    (hDc : ∀ c, R (M (Z c)) = Dc c)
    (hS : (S : B →L[ℂ] B) = schurOperator M U Z P R Dc)
    (hPU : ∀ b, P (U b) = b) (hPZ : ∀ c, P (Z c) = 0)
    (hRU : ∀ b, R (U b) = 0) (hRZ : ∀ c, R (Z c) = c) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.equivOfInverse' M (schurFullInverse M U Z P R Dc S)
    (schurFullInverse_right M U Z P R Dc S hdecomp hDc hS hPU hPZ hRU hRZ)
    (schurFullInverse_left M U Z P R Dc S hdecomp hDc hS)

theorem schurFullInverse_norm (M : E →L[ℂ] E) (U : B →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C) (S : B ≃L[ℂ] B)
    (hU : ‖U‖ ≤ 1) (hZ : ‖Z‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hleft : ‖(Dc.symm : C →L[ℂ] C).comp (R.comp (M.comp U))‖ ≤ 1)
    (hright : ‖(P.comp (M.comp Z)).comp (Dc.symm : C →L[ℂ] C)‖ ≤ 1) :
    ‖schurFullInverse M U Z P R Dc S‖ ≤ 4*‖(S.symm : B →L[ℂ] B)‖+‖(Dc.symm : C →L[ℂ] C)‖ := by
  have he := Composition.complementaryInverse_norm_le_of_local_bounds
    (M.restrictScalars ℝ) (U.restrictScalars ℝ) (Z.restrictScalars ℝ)
    (P.restrictScalars ℝ) (R.restrictScalars ℝ) (Dc.restrictScalars ℝ) (S.restrictScalars ℝ)
    1 1 hU hZ hP hR hleft hright
  change ‖schurFullInverse M U Z P R Dc S‖ ≤
    (1+1)*(1+1)*‖(S.symm : B →L[ℂ] B)‖+‖(Dc.symm : C →L[ℂ] C)‖ at he
  norm_num at he ⊢
  exact he

theorem schur_action (M : E →L[ℂ] E) (U : B →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C)
    (hdecomp : ∀ x, x = U (P x)+Z (R x))
    (hDc : ∀ c, R (M (Z c)) = Dc c) (x : E) :
    schurOperator M U Z P R Dc (P x) = schurResidual M Z P R Dc (M x) :=
  Composition.complementary_schur_action
    (M.restrictScalars ℝ) (U.restrictScalars ℝ) (Z.restrictScalars ℝ)
    (P.restrictScalars ℝ) (R.restrictScalars ℝ) (Dc.restrictScalars ℝ) hdecomp hDc x

#print axioms schurFullInverse_left
#print axioms schurFullInverse_right
#print axioms schurFullInverse_norm

end Maxwell.Continuum.FiniteAuxiliary
