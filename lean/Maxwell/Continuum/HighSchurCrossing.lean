import Maxwell.Continuum.HighSchurKernel
import Maxwell.Continuum.HighSchurVariational
import Maxwell.Continuum.WindowCrossing

/-! A finite singular-parameter cover for a uniformly positive high-block
family. Inversion, finite dimensional reduction and counting are conclusions
of the actual block formulas and quadratic inequalities. -/

noncomputable section

namespace Maxwell.Continuum.HighSchurCrossing

open SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable (W : Set ℝ) (L K : Type*)
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

structure Family where
  high : W → K →ₗ.[ℂ] K
  low : W → L →L[ℂ] L
  coupling : W → L →L[ℂ] K
  high_selfAdjoint : ∀ t, IsSelfAdjoint (high t)
  low_symmetric : ∀ t, (low t).IsSymmetric
  common_domain : ∀ a b, (high a).domain = (high b).domain
  high_coercive : ∀ t (y : (high t).domain),
    (3 / 4 : ℝ) * ‖(y : K)‖ ^ 2 ≤ (inner ℂ (y : K) (high t y)).re
  decrease : ∀ a b : W, (a : ℝ) ≤ b → ∀ (x : L) (y : (high a).domain),
    HighSchur.energy (A := high b) (low b) (coupling b) x
      ⟨(y : K), common_domain a b ▸ y.property⟩ ≤
    HighSchur.energy (low a) (coupling a) x y -
      ((b : ℝ) - a) * (‖x‖ ^ 2 + ‖(y : K)‖ ^ 2)

namespace Family

variable {W L K} (F : Family W L K)

def highInverse (t : W) : BoundedInverse (F.high t) :=
  HighSchur.positiveInverse (F.high t) (F.high_selfAdjoint t)
    (by norm_num : (0 : ℝ) < 3 / 4) (F.high_coercive t)

omit [CompleteSpace L] in
theorem highInverse_norm_le (t : W) : ‖(F.highInverse t).map‖ ≤ 4 / 3 := by
  simpa [highInverse] using HighSchur.positiveInverse_norm_le
    (F.high t) (F.high_selfAdjoint t) (by norm_num : (0 : ℝ) < 3 / 4) (F.high_coercive t)

def effective (t : W) : L →L[ℂ] L :=
  HighSchur.schur (F.low t) (F.coupling t) (F.highInverse t)

theorem effective_symmetric (t : W) : (F.effective t).IsSymmetric :=
  HighSchur.schur_symmetric _ _ _ (F.low_symmetric t) (F.high_selfAdjoint t)

omit [CompleteSpace L] in
theorem high_nonnegative (t : W) (y : (F.high t).domain) :
    0 ≤ (inner ℂ (y : K) (F.high t y)).re := by
  have h := F.high_coercive t y
  nlinarith [sq_nonneg ‖(y : K)‖]

omit [CompleteSpace L] in
theorem high_formalAdjoint (t : W) : (F.high t).IsFormalAdjoint (F.high t) := by
  have h := LinearPMap.adjoint_isFormalAdjoint (F.high_selfAdjoint t).dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp (F.high_selfAdjoint t)] at h

theorem effective_decrease (a b : W) (hab : (a : ℝ) ≤ b) (x : L) :
    (inner ℂ x (F.effective b x)).re ≤ (inner ℂ x (F.effective a x)).re -
      ((b : ℝ) - a) * ‖x‖ ^ 2 :=
  HighSchur.schur_strict_decrease _ _ _ _ (F.highInverse a) (F.highInverse b)
    (F.common_domain a b) (F.high_formalAdjoint b) (F.high_nonnegative b)
    (sub_nonneg.mpr hab) (F.decrease a b hab) x

theorem kernel_finrank_eq (t : W) :
    Module.finrank ℂ (HighSchur.block (F.low t) (F.coupling t) (F.high t)).ker =
      Module.finrank ℂ (F.effective t).ker :=
  HighSchur.kernel_finrank_eq _ _ _

variable [FiniteDimensional ℂ L]

def singularParameters : Finset ℝ :=
  WindowCrossing.singularParameters W (fun t => (F.effective t).toLinearMap)
    F.effective_symmetric F.effective_decrease

theorem singularParameters_card_le : F.singularParameters.card ≤ Module.finrank ℂ L :=
  WindowCrossing.singularParameters_card_le _ _ _ _

theorem mem_singularParameters (t : W) :
    (t : ℝ) ∈ F.singularParameters ↔ (F.effective t).ker ≠ ⊥ :=
  WindowCrossing.mem_singularParameters _ _ _ _ t

/-- A bounded inverse exists at every point outside the finite zero set;
there is no hidden continuous spectrum in the eliminated high block. -/
theorem inverse_iff_not_mem (t : W) :
    Nonempty (BoundedInverse (HighSchur.block (F.low t) (F.coupling t) (F.high t))) ↔
      (t : ℝ) ∉ F.singularParameters := by
  rw [F.mem_singularParameters t, not_not]
  exact HighSchur.block_inverse_iff_schur_ker_eq_bot _ _ (F.highInverse t)

end Family

end Maxwell.Continuum.HighSchurCrossing
