import Maxwell.Composition.SourceIdentity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Full block inversion in the physical norm

The terminal and complementary coordinates are maps into and out of one
normed space. No max norm on a Cartesian product is substituted for the
physical Euclidean norm. Only the local diagonal and Schur operators are
assumed invertible; full invertibility is constructed from their inverses.
-/

namespace Maxwell.Composition

variable {D B C : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]

def complementaryLift (M : D →L[ℝ] D) (U : B →L[ℝ] D)
    (Z : C →L[ℝ] D) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C) : B →L[ℝ] D :=
  U - Z.comp ((Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U)))

def complementaryInverse (M : D →L[ℝ] D) (U : B →L[ℝ] D)
    (Z : C →L[ℝ] D) (P : D →L[ℝ] B) (R : D →L[ℝ] C)
    (Dc : C ≃L[ℝ] C) (S : B ≃L[ℝ] B) : D →L[ℝ] D :=
  (complementaryLift M U Z R Dc).comp
    ((S.symm : B →L[ℝ] B).comp (complementaryResidualMap M Z P R Dc)) +
    Z.comp ((Dc.symm : C →L[ℝ] C).comp R)

private theorem complementary_lower_action
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (M (Z c)) = Dc c) (w : D) :
    R (M w) = R (M (U (P w))) + Dc (R w) := by
  conv_lhs => rw [hdecomp w]
  rw [map_add, map_add, hDc]

/-- Explicit local block inversion gives a left inverse on the full space. -/
theorem complementaryInverse_comp
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C)
    (Dc : C ≃L[ℝ] C) (S : B ≃L[ℝ] B)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (M (Z c)) = Dc c)
    (hS : (S : B →L[ℝ] B) = brightSchurOperator M U Z P R Dc) :
    (complementaryInverse M U Z P R Dc S).comp M = ContinuousLinearMap.id ℝ D := by
  ext w
  have hcore : S.symm (complementaryResidualMap M Z P R Dc (M w)) = P w := by
    rw [← complementary_schur_action M U Z P R Dc hdecomp hDc w, ← hS]
    exact S.symm_apply_apply _
  simp only [ContinuousLinearMap.comp_apply, complementaryInverse, complementaryLift,
    add_apply, sub_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply]
  rw [hcore, complementary_lower_action M U Z P R Dc hdecomp hDc w]
  simp only [map_add, ContinuousLinearEquiv.symm_apply_apply]
  calc
    _ = U (P w) + Z (R w) := by abel
    _ = w := (hdecomp w).symm

/-- The other inverse identity follows from the four coordinate identities;
there is no finite-dimensional surjectivity shortcut. -/
theorem comp_complementaryInverse
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C)
    (Dc : C ≃L[ℝ] C) (S : B ≃L[ℝ] B)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (M (Z c)) = Dc c)
    (hS : (S : B →L[ℝ] B) = brightSchurOperator M U Z P R Dc)
    (hPU : ∀ b, P (U b) = b) (hPZ : ∀ c, P (Z c) = 0)
    (hRU : ∀ b, R (U b) = 0) (hRZ : ∀ c, R (Z c) = c) :
    M.comp (complementaryInverse M U Z P R Dc S) = ContinuousLinearMap.id ℝ D := by
  ext d
  let w := complementaryInverse M U Z P R Dc S d
  let q := S.symm (complementaryResidualMap M Z P R Dc d)
  have hPw : P w = q := by
    simp [w, q, complementaryInverse, complementaryLift, hPU, hPZ]
  have hRw : R w = -(Dc.symm (R (M (U q)))) + Dc.symm (R d) := by
    simp [w, q, complementaryInverse, complementaryLift, hRU, hRZ]
  have hRMw : R (M w) = R d := by
    rw [complementary_lower_action M U Z P R Dc hdecomp hDc w, hPw, hRw]
    simp
  have hres : complementaryResidualMap M Z P R Dc (M w) =
      complementaryResidualMap M Z P R Dc d := by
    rw [← complementary_schur_action M U Z P R Dc hdecomp hDc w, ← hS, hPw]
    exact S.apply_symm_apply _
  have hPMw : P (M w) = P d := by
    simp only [complementaryResidualMap, sub_apply, ContinuousLinearMap.comp_apply] at hres
    rw [hRMw] at hres
    exact (sub_left_inj).mp hres
  change M w = d
  calc
    M w = U (P (M w)) + Z (R (M w)) := hdecomp _
    _ = U (P d) + Z (R d) := by rw [hPMw, hRMw]
    _ = d := (hdecomp d).symm

/-- Full-space invertibility is a conclusion of local block invertibility. -/
def complementaryEquiv
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C)
    (Dc : C ≃L[ℝ] C) (S : B ≃L[ℝ] B)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (M (Z c)) = Dc c)
    (hS : (S : B →L[ℝ] B) = brightSchurOperator M U Z P R Dc)
    (hPU : ∀ b, P (U b) = b) (hPZ : ∀ c, P (Z c) = 0)
    (hRU : ∀ b, R (U b) = 0) (hRZ : ∀ c, R (Z c) = c) : D ≃L[ℝ] D :=
  ContinuousLinearEquiv.equivOfInverse' M (complementaryInverse M U Z P R Dc S)
    (comp_complementaryInverse M U Z P R Dc S hdecomp hDc hS hPU hPZ hRU hRZ)
    (complementaryInverse_comp M U Z P R Dc S hdecomp hDc hS)

/-- Exact operator-norm bound for the constructed inverse in the common
physical space. -/
theorem complementaryInverse_norm_le
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C)
    (Dc : C ≃L[ℝ] C) (S : B ≃L[ℝ] B) :
    ‖complementaryInverse M U Z P R Dc S‖ ≤
      ‖complementaryLift M U Z R Dc‖ * ‖(S.symm : B →L[ℝ] B)‖ *
        ‖complementaryResidualMap M Z P R Dc‖ +
      ‖Z‖ * ‖(Dc.symm : C →L[ℝ] C)‖ * ‖R‖ := by
  rw [complementaryInverse]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc
      _ ≤ ‖complementaryLift M U Z R Dc‖ *
          ‖(S.symm : B →L[ℝ] B).comp (complementaryResidualMap M Z P R Dc)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖complementaryLift M U Z R Dc‖ *
          (‖(S.symm : B →L[ℝ] B)‖ * ‖complementaryResidualMap M Z P R Dc‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ ‖Z‖ * ‖(Dc.symm : C →L[ℝ] C).comp R‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Z‖ * (‖(Dc.symm : C →L[ℝ] C)‖ * ‖R‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = _ := by ring

/-- Local lower mixed-block control bounds the corrected injection. -/
theorem complementaryLift_norm_le
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C) (l : ℝ)
    (hU : ‖U‖ ≤ 1) (hZ : ‖Z‖ ≤ 1)
    (hleft : ‖(Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U))‖ ≤ l) :
    ‖complementaryLift M U Z R Dc‖ ≤ 1 + l := by
  have hl : 0 ≤ l := (norm_nonneg _).trans hleft
  calc
    _ ≤ ‖U‖ + ‖Z.comp ((Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U)))‖ :=
      norm_sub_le _ _
    _ ≤ ‖U‖ + ‖Z‖ * ‖(Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U))‖ :=
      add_le_add_right (ContinuousLinearMap.opNorm_comp_le _ _) _
    _ ≤ 1 + 1 * l := by gcongr
    _ = 1 + l := by ring

/-- Local upper mixed-block control bounds the corrected projection. -/
theorem complementaryResidualMap_norm_le
    (M : D →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C) (r : ℝ)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hright : ‖(P.comp (M.comp Z)).comp (Dc.symm : C →L[ℝ] C)‖ ≤ r) :
    ‖complementaryResidualMap M Z P R Dc‖ ≤ 1 + r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hright
  rw [complementaryResidualMap, ← ContinuousLinearMap.comp_assoc]
  calc
    _ ≤ ‖P‖ + ‖((P.comp (M.comp Z)).comp (Dc.symm : C →L[ℝ] C)).comp R‖ :=
      norm_sub_le _ _
    _ ≤ ‖P‖ + ‖(P.comp (M.comp Z)).comp (Dc.symm : C →L[ℝ] C)‖ * ‖R‖ :=
      add_le_add_right (ContinuousLinearMap.opNorm_comp_le _ _) _
    _ ≤ 1 + r * 1 := by gcongr
    _ = 1 + r := by ring

/-- Quantitative block inversion retains separate upper and lower mixed
blocks, so symmetry need not be silently inferred. -/
theorem complementaryInverse_norm_le_of_local_bounds
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C)
    (Dc : C ≃L[ℝ] C) (S : B ≃L[ℝ] B) (l r : ℝ)
    (hU : ‖U‖ ≤ 1) (hZ : ‖Z‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hleft : ‖(Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U))‖ ≤ l)
    (hright : ‖(P.comp (M.comp Z)).comp (Dc.symm : C →L[ℝ] C)‖ ≤ r) :
    ‖complementaryInverse M U Z P R Dc S‖ ≤
      (1 + l) * (1 + r) * ‖(S.symm : B →L[ℝ] B)‖ + ‖(Dc.symm : C →L[ℝ] C)‖ := by
  have hlift := complementaryLift_norm_le M U Z R Dc l hU hZ hleft
  have hproj := complementaryResidualMap_norm_le M Z P R Dc r hP hR hright
  have hl : 0 ≤ 1 + l := (norm_nonneg _).trans hlift
  have hr : 0 ≤ 1 + r := (norm_nonneg _).trans hproj
  calc
    _ ≤ ‖complementaryLift M U Z R Dc‖ * ‖(S.symm : B →L[ℝ] B)‖ *
        ‖complementaryResidualMap M Z P R Dc‖ +
        ‖Z‖ * ‖(Dc.symm : C →L[ℝ] C)‖ * ‖R‖ :=
      complementaryInverse_norm_le M U Z P R Dc S
    _ ≤ (1 + l) * ‖(S.symm : B →L[ℝ] B)‖ * (1 + r) +
        1 * ‖(Dc.symm : C →L[ℝ] C)‖ * 1 := by gcongr
    _ = _ := by ring

/-- The full-space `Q_M` estimate follows from the two local inverse bounds
and mixed-block products bounded by one. -/
theorem complementary_full_inverse_norm_le
    (M : D →L[ℝ] D) (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C)
    (Dc : C ≃L[ℝ] C) (S : B ≃L[ℝ] B)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (M (Z c)) = Dc c)
    (hS : (S : B →L[ℝ] B) = brightSchurOperator M U Z P R Dc)
    (hPU : ∀ b, P (U b) = b) (hPZ : ∀ c, P (Z c) = 0)
    (hRU : ∀ b, R (U b) = 0) (hRZ : ∀ c, R (Z c) = c)
    (hU : ‖U‖ ≤ 1) (hZ : ‖Z‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hleft : ‖(Dc.symm : C →L[ℝ] C).comp (R.comp (M.comp U))‖ ≤ 1)
    (hright : ‖(P.comp (M.comp Z)).comp (Dc.symm : C →L[ℝ] C)‖ ≤ 1) :
    ‖((complementaryEquiv M U Z P R Dc S hdecomp hDc hS hPU hPZ hRU hRZ).symm :
        D →L[ℝ] D)‖ ≤
      4 * (‖(S.symm : B →L[ℝ] B)‖ + ‖(Dc.symm : C →L[ℝ] C)‖) := by
  change ‖complementaryInverse M U Z P R Dc S‖ ≤ _
  have h := complementaryInverse_norm_le_of_local_bounds M U Z P R Dc S
    1 1 hU hZ hP hR hleft hright
  nlinarith [norm_nonneg (Dc.symm : C →L[ℝ] C)]

end Maxwell.Composition
