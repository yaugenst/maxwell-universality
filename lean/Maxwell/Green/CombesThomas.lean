import Maxwell.Spectral.Lattice
import Maxwell.Green.DistanceWeight
import Maxwell.Composition.Woodbury
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FieldSimp

/-!
# Clipped exponential conjugation on the infinite Yee lattice

Weights act on the actual square-summable complex field. Local variation of
a bounded distance potential controls conjugation of the finite stencil;
its resolvent decay is an operator-norm statement between whole sets.
-/

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace Maxwell.Green

open Maxwell.Spectral
open scoped InnerProduct

variable {ι : Type*}

/-- A scalar exponential increment is controlled by the exponential of an
absolute increment. -/
theorem abs_exp_sub_one_le {x a : ℝ} (hx : |x| ≤ a) :
    |Real.exp x - 1| ≤ Real.exp a - 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  apply abs_le.mpr
  constructor
  · linarith [Real.add_one_le_exp x, Real.add_one_le_exp a]
  · linarith [Real.exp_le_exp.mpr hhi]

/-- The bounded positive exponential multiplier associated with a clipped
nonnegative potential. -/
def exponentialWeight (φ : ι → ℝ) (μ cap : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap) : SequenceL2 ι →L[ℂ] SequenceL2 ι :=
  realSequenceMultiplier (fun i => Real.exp (μ * φ i)) (Real.exp (μ * cap))
    (Real.exp_pos _).le (fun i => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hφ i).2 hμ))

def inverseExponentialWeight (φ : ι → ℝ) (μ cap : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap) : SequenceL2 ι →L[ℂ] SequenceL2 ι :=
  realSequenceMultiplier (fun i => Real.exp (-(μ * φ i))) 1 (by norm_num)
    (fun i => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact (Real.exp_le_one_iff).mpr (neg_nonpos.mpr (mul_nonneg hμ (hφ i).1)))

@[simp] theorem exponentialWeight_apply (φ : ι → ℝ) (μ cap : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap) (f : SequenceL2 ι) (i : ι) :
    exponentialWeight φ μ cap hμ hφ f i = (Real.exp (μ * φ i) : ℂ) * f i := rfl

@[simp] theorem inverseExponentialWeight_apply (φ : ι → ℝ) (μ cap : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap) (f : SequenceL2 ι) (i : ι) :
    inverseExponentialWeight φ μ cap hμ hφ f i =
      (Real.exp (-(μ * φ i)) : ℂ) * f i := rfl

/-- Clipping makes both exponential weights bounded, so conjugation is a
continuous linear equivalence on the full infinite field space. -/
def exponentialEquiv (φ : ι → ℝ) (μ cap : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap) : SequenceL2 ι ≃L[ℂ] SequenceL2 ι :=
  ContinuousLinearEquiv.equivOfInverse (exponentialWeight φ μ cap hμ hφ)
    (inverseExponentialWeight φ μ cap hμ hφ)
    (by
      intro f
      ext i
      simp only [inverseExponentialWeight_apply, exponentialWeight_apply, ← mul_assoc,
        ← Complex.ofReal_mul, ← Real.exp_add]
      simp)
    (by
      intro f
      ext i
      simp only [inverseExponentialWeight_apply, exponentialWeight_apply, ← mul_assoc,
        ← Complex.ofReal_mul, ← Real.exp_add]
      simp)

/-- Conjugation by an actual bounded equivalence. -/
def weightConjugate (W : SequenceL2 ι ≃L[ℂ] SequenceL2 ι)
    (A : SequenceL2 ι →L[ℂ] SequenceL2 ι) : SequenceL2 ι →L[ℂ] SequenceL2 ι :=
  (W : SequenceL2 ι →L[ℂ] SequenceL2 ι).comp
    (A.comp (W.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι))

/-- The coordinate-pullback form of the infinite stencil. -/
def sequencePullback (e : Equiv.Perm ι) : SequenceL2 ι →L[ℂ] SequenceL2 ι :=
  (sequenceReindex e).toLinearIsometry.toContinuousLinearMap

@[simp] theorem sequencePullback_apply (e : Equiv.Perm ι) (f : SequenceL2 ι) (i : ι) :
    sequencePullback e f i = f (e i) := rfl

theorem sequencePullback_norm_le (e : Equiv.Perm ι) : ‖sequencePullback e‖ ≤ 1 :=
  (sequenceReindex e).toLinearIsometry.norm_toContinuousLinearMap_le

/-- Every local pullback acquires only its local exponential ratio. -/
theorem pullback_conjugation_norm_le (φ : ι → ℝ) (μ cap r : ℝ)
    (hμ : 0 ≤ μ) (hr : 0 ≤ r) (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap)
    (e : Equiv.Perm ι) (hlocal : ∀ i, |φ i - φ (e i)| ≤ r) :
    ‖weightConjugate (exponentialEquiv φ μ cap hμ hφ) (sequencePullback e) -
        sequencePullback e‖ ≤ Real.exp (μ * r) - 1 := by
  let b := Real.exp (μ * r) - 1
  have hb : 0 ≤ b := by dsimp [b]; linarith [Real.one_le_exp (mul_nonneg hμ hr)]
  let a := fun i => Real.exp (μ * (φ i - φ (e i))) - 1
  have ha : ∀ i, |a i| ≤ b := by
    intro i
    apply abs_exp_sub_one_le
    rw [abs_mul, abs_of_nonneg hμ]
    exact mul_le_mul_of_nonneg_left (hlocal i) hμ
  have hid : weightConjugate (exponentialEquiv φ μ cap hμ hφ) (sequencePullback e) -
      sequencePullback e = (realSequenceMultiplier a b hb ha).comp (sequencePullback e) := by
    ext f i
    change (Real.exp (μ * φ i) : ℂ) *
        ((Real.exp (-(μ * φ (e i))) : ℂ) * f (e i)) - f (e i) =
      ((Real.exp (μ * (φ i - φ (e i))) - 1 : ℝ) : ℂ) * f (e i)
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show μ * φ i + -(μ * φ (e i)) = μ * (φ i - φ (e i)) by ring]
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖realSequenceMultiplier a b hb ha‖ * ‖sequencePullback e‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ b * 1 := mul_le_mul (realSequenceMultiplier_norm_le a b hb ha)
      (sequencePullback_norm_le e) (norm_nonneg _) hb
    _ = Real.exp (μ * r) - 1 := by simp [b]

@[simp] theorem weightConjugate_add (W : SequenceL2 ι ≃L[ℂ] SequenceL2 ι)
    (A B : SequenceL2 ι →L[ℂ] SequenceL2 ι) :
    weightConjugate W (A + B) = weightConjugate W A + weightConjugate W B := by
  ext f
  simp [weightConjugate]

@[simp] theorem weightConjugate_sub (W : SequenceL2 ι ≃L[ℂ] SequenceL2 ι)
    (A B : SequenceL2 ι →L[ℂ] SequenceL2 ι) :
    weightConjugate W (A - B) = weightConjugate W A - weightConjugate W B := by
  ext f
  simp [weightConjugate]

@[simp] theorem weightConjugate_smul (W : SequenceL2 ι ≃L[ℂ] SequenceL2 ι)
    (a : ℂ) (A : SequenceL2 ι →L[ℂ] SequenceL2 ι) :
    weightConjugate W (a • A) = a • weightConjugate W A := by
  ext f
  simp [weightConjugate]

theorem weightConjugate_comp (W : SequenceL2 ι ≃L[ℂ] SequenceL2 ι)
    (A B : SequenceL2 ι →L[ℂ] SequenceL2 ι) :
    weightConjugate W (A.comp B) = (weightConjugate W A).comp (weightConjugate W B) := by
  ext f
  simp [weightConjugate]

@[simp] theorem sequencePullback_adjoint (e : Equiv.Perm ι) :
    (sequencePullback e).adjoint = sequencePullback e.symm := by
  exact (sequenceReindex e).adjoint_eq_symm

def fourPullbackCurl (e₁ e₂ e₃ e₄ : Equiv.Perm ι) : SequenceL2 ι →L[ℂ] SequenceL2 ι :=
  sequencePullback e₁ - sequencePullback e₂ - sequencePullback e₃ + sequencePullback e₄

private theorem norm_four_signed_le (A B C D : SequenceL2 ι →L[ℂ] SequenceL2 ι)
    (t : ℝ) (hA : ‖A‖ ≤ t) (hB : ‖B‖ ≤ t) (hC : ‖C‖ ≤ t) (hD : ‖D‖ ≤ t) :
    ‖A - B - C + D‖ ≤ 4 * t := by
  calc
    _ ≤ ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by
      grw [norm_add_le, norm_sub_le, norm_sub_le]
    _ ≤ 4 * t := by linarith

theorem fourPullbackCurl_norm_le (e₁ e₂ e₃ e₄ : Equiv.Perm ι) :
    ‖fourPullbackCurl e₁ e₂ e₃ e₄‖ ≤ 4 := by
  simpa only [fourPullbackCurl, mul_one] using
    norm_four_signed_le _ _ _ _ 1 (sequencePullback_norm_le e₁)
      (sequencePullback_norm_le e₂) (sequencePullback_norm_le e₃) (sequencePullback_norm_le e₄)

theorem fourPullbackCurl_conjugation_norm_le (φ : ι → ℝ) (μ cap r : ℝ)
    (hμ : 0 ≤ μ) (hr : 0 ≤ r) (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap)
    (e₁ e₂ e₃ e₄ : Equiv.Perm ι)
    (h₁ : ∀ i, |φ i - φ (e₁ i)| ≤ r) (h₂ : ∀ i, |φ i - φ (e₂ i)| ≤ r)
    (h₃ : ∀ i, |φ i - φ (e₃ i)| ≤ r) (h₄ : ∀ i, |φ i - φ (e₄ i)| ≤ r) :
    ‖weightConjugate (exponentialEquiv φ μ cap hμ hφ) (fourPullbackCurl e₁ e₂ e₃ e₄) -
        fourPullbackCurl e₁ e₂ e₃ e₄‖ ≤ 4 * (Real.exp (μ * r) - 1) := by
  let W := exponentialEquiv φ μ cap hμ hφ
  have hsplit : weightConjugate W (fourPullbackCurl e₁ e₂ e₃ e₄) -
      fourPullbackCurl e₁ e₂ e₃ e₄ =
      (weightConjugate W (sequencePullback e₁) - sequencePullback e₁) -
      (weightConjugate W (sequencePullback e₂) - sequencePullback e₂) -
      (weightConjugate W (sequencePullback e₃) - sequencePullback e₃) +
      (weightConjugate W (sequencePullback e₄) - sequencePullback e₄) := by
    simp only [fourPullbackCurl, weightConjugate_add, weightConjugate_sub]
    abel
  rw [hsplit]
  exact norm_four_signed_le _ _ _ _ _
    (pullback_conjugation_norm_le φ μ cap r hμ hr hφ e₁ h₁)
    (pullback_conjugation_norm_le φ μ cap r hμ hr hφ e₂ h₂)
    (pullback_conjugation_norm_le φ μ cap r hμ hr hφ e₃ h₃)
    (pullback_conjugation_norm_le φ μ cap r hμ hr hφ e₄ h₄)

private theorem inverse_local_bound (φ : ι → ℝ) (e : Equiv.Perm ι) (r : ℝ)
    (h : ∀ i, |φ i - φ (e i)| ≤ r) : ∀ i, |φ i - φ (e.symm i)| ≤ r := by
  intro i
  have hi := h (e.symm i)
  rw [e.apply_symm_apply, abs_sub_comm] at hi
  exact hi

theorem fourPullbackCurl_adjoint_conjugation_norm_le (φ : ι → ℝ) (μ cap r : ℝ)
    (hμ : 0 ≤ μ) (hr : 0 ≤ r) (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap)
    (e₁ e₂ e₃ e₄ : Equiv.Perm ι)
    (h₁ : ∀ i, |φ i - φ (e₁ i)| ≤ r) (h₂ : ∀ i, |φ i - φ (e₂ i)| ≤ r)
    (h₃ : ∀ i, |φ i - φ (e₃ i)| ≤ r) (h₄ : ∀ i, |φ i - φ (e₄ i)| ≤ r) :
    ‖weightConjugate (exponentialEquiv φ μ cap hμ hφ)
        (fourPullbackCurl e₁ e₂ e₃ e₄).adjoint -
        (fourPullbackCurl e₁ e₂ e₃ e₄).adjoint‖ ≤ 4 * (Real.exp (μ * r) - 1) := by
  have hadj : (fourPullbackCurl e₁ e₂ e₃ e₄).adjoint =
      fourPullbackCurl e₁.symm e₂.symm e₃.symm e₄.symm := by
    simp [fourPullbackCurl]
  rw [hadj]
  exact fourPullbackCurl_conjugation_norm_le φ μ cap r hμ hr hφ _ _ _ _
    (inverse_local_bound φ e₁ r h₁) (inverse_local_bound φ e₂ r h₂)
    (inverse_local_bound φ e₃ r h₃) (inverse_local_bound φ e₄ r h₄)

/-- Scalar material multiplication commutes with the exponential weight
exactly, regardless of its periodicity. -/
theorem multiplier_conjugation (φ m : ι → ℝ) (μ cap K : ℝ)
    (hμ : 0 ≤ μ) (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap)
    (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K) :
    weightConjugate (exponentialEquiv φ μ cap hμ hφ) (realSequenceMultiplier m K hK hm) =
      realSequenceMultiplier m K hK hm := by
  ext f i
  change (Real.exp (μ * φ i) : ℂ) * ((m i : ℂ) *
      ((Real.exp (-(μ * φ i)) : ℂ) * f i)) = (m i : ℂ) * f i
  calc
    _ = ((Real.exp (μ * φ i) : ℂ) * (Real.exp (-(μ * φ i)) : ℂ)) *
        ((m i : ℂ) * f i) := by ring
    _ = (m i : ℂ) * f i := by rw [← Complex.ofReal_mul, ← Real.exp_add]; simp

/-- The two curl factors give sixteen local transport terms. Bounding the
two factors preserves this constant without any volume dependence. -/
theorem curl_square_conjugation_norm_le (φ : ι → ℝ) (μ cap r : ℝ)
    (hμ : 0 ≤ μ) (hr : 0 ≤ r) (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap)
    (e₁ e₂ e₃ e₄ : Equiv.Perm ι)
    (h₁ : ∀ i, |φ i - φ (e₁ i)| ≤ r) (h₂ : ∀ i, |φ i - φ (e₂ i)| ≤ r)
    (h₃ : ∀ i, |φ i - φ (e₃ i)| ≤ r) (h₄ : ∀ i, |φ i - φ (e₄ i)| ≤ r) :
    ‖weightConjugate (exponentialEquiv φ μ cap hμ hφ)
        ((fourPullbackCurl e₁ e₂ e₃ e₄).adjoint.comp (fourPullbackCurl e₁ e₂ e₃ e₄)) -
        (fourPullbackCurl e₁ e₂ e₃ e₄).adjoint.comp (fourPullbackCurl e₁ e₂ e₃ e₄)‖ ≤
      16 * (Real.exp (2 * μ * r) - 1) := by
  let W := exponentialEquiv φ μ cap hμ hφ
  let C := fourPullbackCurl e₁ e₂ e₃ e₄
  have hC : ‖C‖ ≤ 4 := fourPullbackCurl_norm_le e₁ e₂ e₃ e₄
  have hCa : ‖C.adjoint‖ ≤ 4 := by simpa only [LinearIsometryEquiv.norm_map] using hC
  have hdiff : ‖weightConjugate W C - C‖ ≤ 4 * (Real.exp (μ * r) - 1) :=
    fourPullbackCurl_conjugation_norm_le φ μ cap r hμ hr hφ e₁ e₂ e₃ e₄ h₁ h₂ h₃ h₄
  have hadiff : ‖weightConjugate W C.adjoint - C.adjoint‖ ≤ 4 * (Real.exp (μ * r) - 1) :=
    fourPullbackCurl_adjoint_conjugation_norm_le φ μ cap r hμ hr hφ e₁ e₂ e₃ e₄ h₁ h₂ h₃ h₄
  have hconj : ‖weightConjugate W C‖ ≤ 4 * Real.exp (μ * r) := by
    have htriangle : ‖weightConjugate W C‖ ≤ ‖weightConjugate W C - C‖ + ‖C‖ :=
      norm_le_norm_sub_add _ _
    linarith
  have hexp0 : 0 ≤ Real.exp (μ * r) - 1 := by
    linarith [Real.one_le_exp (mul_nonneg hμ hr)]
  have hexp : Real.exp (2 * μ * r) = Real.exp (μ * r) ^ 2 := by
    rw [show 2 * μ * r = μ * r + μ * r by ring, Real.exp_add, pow_two]
  have hid : weightConjugate W (C.adjoint.comp C) - C.adjoint.comp C =
      (weightConjugate W C.adjoint - C.adjoint).comp (weightConjugate W C) +
        C.adjoint.comp (weightConjugate W C - C) := by
    rw [weightConjugate_comp]
    ext1 f
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  change ‖weightConjugate W (C.adjoint.comp C) - C.adjoint.comp C‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖(weightConjugate W C.adjoint - C.adjoint).comp (weightConjugate W C)‖ +
        ‖C.adjoint.comp (weightConjugate W C - C)‖ := norm_add_le _ _
    _ ≤ ‖weightConjugate W C.adjoint - C.adjoint‖ * ‖weightConjugate W C‖ +
        ‖C.adjoint‖ * ‖weightConjugate W C - C‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (4 * (Real.exp (μ * r) - 1)) * (4 * Real.exp (μ * r)) +
        4 * (4 * (Real.exp (μ * r) - 1)) := by gcongr
    _ = 16 * (Real.exp (2 * μ * r) - 1) := by rw [hexp]; ring

/-- Conjugating the actual infinite Yee electric operator changes only its
finite curl stencil. The material term contributes zero. -/
theorem electric_conjugation_norm_le (φ : Lattice.Edge → ℝ) (μ cap r : ℝ)
    (hμ : 0 ≤ μ) (hr : 0 ≤ r) (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap)
    (m : Lattice.Edge → ℝ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K)
    (h₁ : ∀ i, |φ i - φ (Lattice.fieldPermutation Lattice.directionCycle.symm
      (fun d => Lattice.unitSite (d + 1)) i)| ≤ r)
    (h₂ : ∀ i, |φ i - φ (Lattice.fieldPermutation Lattice.directionCycle.symm
      (fun _ => 0) i)| ≤ r)
    (h₃ : ∀ i, |φ i - φ (Lattice.fieldPermutation Lattice.directionCycle
      (fun d => Lattice.unitSite (d + 2)) i)| ≤ r)
    (h₄ : ∀ i, |φ i - φ (Lattice.fieldPermutation Lattice.directionCycle
      (fun _ => 0) i)| ≤ r) :
    ‖weightConjugate (exponentialEquiv φ μ cap hμ hφ) (Lattice.electricOperator m K hK hm) -
        Lattice.electricOperator m K hK hm‖ ≤ 16 * (Real.exp (2 * μ * r) - 1) := by
  rw [Lattice.electricOperator, weightConjugate_sub, weightConjugate_smul,
    multiplier_conjugation]
  have hid (A B D : Lattice.Field →L[ℂ] Lattice.Field) : (A - D) - (B - D) = A - B := by abel
  rw [hid]
  exact curl_square_conjugation_norm_le φ μ cap r hμ hr hφ _ _ _ _ h₁ h₂ h₃ h₄

/-- The concrete clipped distance from an arbitrary source union meets every
stencil hypothesis with one lattice step. -/
theorem clippedDistance_electric_conjugation_norm_le
    (source : Set Lattice.Edge) (cap μ : ℝ) (hcap : 0 ≤ cap) (hμ : 0 ≤ μ)
    (m : Lattice.Edge → ℝ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K) :
    ‖weightConjugate (exponentialEquiv (clippedDistance source cap) μ cap hμ
        (clippedDistance_bounds source cap hcap)) (Lattice.electricOperator m K hK hm) -
        Lattice.electricOperator m K hK hm‖ ≤ 16 * (Real.exp (2 * μ) - 1) := by
  have h := electric_conjugation_norm_le (clippedDistance source cap) μ cap 1 hμ (by norm_num)
    (clippedDistance_bounds source cap hcap) m K hK hm
    (fun i => by rw [abs_sub_comm]; exact clippedDistance_yee_step source cap _ _ i)
    (fun i => by rw [clippedDistance_component_permutation]; simp)
    (fun i => by rw [abs_sub_comm]; exact clippedDistance_yee_step source cap _ _ i)
    (fun i => by rw [clippedDistance_component_permutation]; simp)
  simpa only [mul_one] using h

/-- Coordinate projection onto an arbitrary (possibly infinite) set. -/
def sequenceCut (s : Set ι) : SequenceL2 ι →L[ℂ] SequenceL2 ι := by
  classical
  exact realSequenceMultiplier (fun i => if i ∈ s then 1 else 0) 1 (by norm_num)
    (fun i => by split_ifs <;> norm_num)

@[simp] theorem sequenceCut_apply (s : Set ι) (f : SequenceL2 ι) (i : ι) :
    sequenceCut s f i = if i ∈ s then f i else 0 := by
  classical
  by_cases hi : i ∈ s <;> simp [sequenceCut, hi]

theorem sequenceCut_norm_le (s : Set ι) : ‖sequenceCut s‖ ≤ 1 := by
  classical
  exact realSequenceMultiplier_norm_le _ _ _ _

def conjugateEquiv (W H : SequenceL2 ι ≃L[ℂ] SequenceL2 ι) :
    SequenceL2 ι ≃L[ℂ] SequenceL2 ι := W.symm.trans (H.trans W)

/-- The inverse of the conjugated operator has the factor-two Neumann
bound. Similarity identifies the constructed perturbed inverse exactly. -/
theorem nearby_inverse_norm_le_two (H B : SequenceL2 ι ≃L[ℂ] SequenceL2 ι)
    (hsmall : ‖(H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ *
      ‖(B : SequenceL2 ι →L[ℂ] SequenceL2 ι) - (H : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ ≤ (1 : ℝ) / 2) :
    ‖(B.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ ≤
      2 * ‖(H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ := by
  let Δ := (B : SequenceL2 ι →L[ℂ] SequenceL2 ι) - (H : SequenceL2 ι →L[ℂ] SequenceL2 ι)
  have hlt : ‖(H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ * ‖Δ‖ < 1 := by
    linarith
  have heq : Composition.perturbationEquiv H Δ hlt = B := by
    apply ContinuousLinearEquiv.ext
    funext f
    change (Composition.perturbationEquiv H Δ hlt : SequenceL2 ι →L[ℂ] SequenceL2 ι) f = _
    rw [Composition.perturbationEquiv_toContinuousLinearMap]
    simp only [Δ, add_apply, sub_apply, ContinuousLinearEquiv.coe_coe]
    abel
  have h := Composition.perturbation_full_inverse_norm_le H Δ hlt
  rw [heq] at h
  apply h.trans
  apply (div_le_iff₀ (sub_pos.mpr hlt)).mpr
  have hmul := mul_le_mul_of_nonneg_left hsmall
    (norm_nonneg (H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι))
  dsimp [Δ] at *
  nlinarith

theorem conjugate_inverse_norm_le_two (W H : SequenceL2 ι ≃L[ℂ] SequenceL2 ι)
    (hsmall : ‖(H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ *
      ‖weightConjugate W H - (H : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ ≤ (1 : ℝ) / 2) :
    ‖((conjugateEquiv W H).symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ ≤
      2 * ‖(H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ :=
  nearby_inverse_norm_le_two H (conjugateEquiv W H) hsmall

theorem source_weight_cut (φ : ι → ℝ) (μ cap : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap) (source : Set ι)
    (hsource : ∀ i ∈ source, φ i = 0) :
    (exponentialEquiv φ μ cap hμ hφ : SequenceL2 ι →L[ℂ] SequenceL2 ι).comp
      (sequenceCut source) = sequenceCut source := by
  ext f i
  change (Real.exp (μ * φ i) : ℂ) * sequenceCut source f i = sequenceCut source f i
  by_cases hi : i ∈ source
  · simp [hi, hsource i hi]
  · simp [hi]

theorem target_inverse_weight_cut_norm_le (φ : ι → ℝ) (μ cap d : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap) (target : Set ι)
    (htarget : ∀ i ∈ target, d ≤ φ i) :
    ‖(sequenceCut target).comp
      ((exponentialEquiv φ μ cap hμ hφ).symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ ≤
      Real.exp (-μ * d) := by
  classical
  let a := fun i => if i ∈ target then Real.exp (-(μ * φ i)) else 0
  have ha : ∀ i, |a i| ≤ Real.exp (-μ * d) := by
    intro i
    dsimp [a]
    split_ifs with hi
    · rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (htarget i hi) hμ]
    · simp only [abs_zero]
      exact (Real.exp_pos _).le
  have hid : (sequenceCut target).comp
      ((exponentialEquiv φ μ cap hμ hφ).symm : SequenceL2 ι →L[ℂ] SequenceL2 ι) =
      realSequenceMultiplier a (Real.exp (-μ * d)) (Real.exp_pos _).le ha := by
    ext f i
    simp only [ContinuousLinearMap.comp_apply, sequenceCut_apply]
    change (if i ∈ target then (Real.exp (-(μ * φ i)) : ℂ) * f i else 0) =
      ((if i ∈ target then Real.exp (-(μ * φ i)) else 0 : ℝ) : ℂ) * f i
    split_ifs <;> simp
  rw [hid]
  exact realSequenceMultiplier_norm_le _ _ _ _

/-- Whole-set resolvent decay follows from one exponential weight. Neither
set cardinality appears in the estimate. -/
theorem weighted_set_resolvent_bound_of_conjugate_inverse
    (φ : ι → ℝ) (μ cap d : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap)
    (H : SequenceL2 ι ≃L[ℂ] SequenceL2 ι) (source target : Set ι)
    (hsource : ∀ i ∈ source, φ i = 0) (htarget : ∀ i ∈ target, d ≤ φ i)
    (bound : ℝ)
    (hbound : ‖((conjugateEquiv (exponentialEquiv φ μ cap hμ hφ) H).symm :
      SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ ≤ bound) :
    ‖(sequenceCut target).comp ((H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι).comp
        (sequenceCut source))‖ ≤
      bound * Real.exp (-μ * d) := by
  let W := exponentialEquiv φ μ cap hμ hφ
  let B := conjugateEquiv W H
  have hfactor : (sequenceCut target).comp
      ((H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι).comp (sequenceCut source)) =
      ((sequenceCut target).comp (W.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)).comp
        ((B.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι).comp (sequenceCut source)) := by
    have hs := source_weight_cut φ μ cap hμ hφ source hsource
    have hsid (f : SequenceL2 ι) : W.symm (sequenceCut source f) = sequenceCut source f := by
      apply W.injective
      rw [W.apply_symm_apply]
      exact (congrArg (fun T : SequenceL2 ι →L[ℂ] SequenceL2 ι => T f) hs).symm
    ext1 f
    change sequenceCut target (H.symm (sequenceCut source f)) =
      sequenceCut target (W.symm (W (H.symm (W.symm (sequenceCut source f)))))
    rw [W.symm_apply_apply, hsid]
  rw [hfactor]
  have hB : ‖(B.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ ≤ bound := hbound
  have hbound0 : 0 ≤ bound := (norm_nonneg _).trans hB
  have htargetnorm := target_inverse_weight_cut_norm_le φ μ cap d hμ hφ target htarget
  calc
    _ ≤ ‖(sequenceCut target).comp (W.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ *
        ‖(B.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι).comp (sequenceCut source)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(sequenceCut target).comp (W.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ *
        (‖(B.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ * ‖sequenceCut source‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.exp (-μ * d) * (bound * 1) := by
      gcongr
      exact sequenceCut_norm_le source
    _ = _ := by ring

theorem weighted_set_resolvent_bound (φ : ι → ℝ) (μ cap d : ℝ) (hμ : 0 ≤ μ)
    (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ cap)
    (H : SequenceL2 ι ≃L[ℂ] SequenceL2 ι) (source target : Set ι)
    (hsource : ∀ i ∈ source, φ i = 0) (htarget : ∀ i ∈ target, d ≤ φ i)
    (hsmall : ‖(H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ *
      ‖weightConjugate (exponentialEquiv φ μ cap hμ hφ) H -
        (H : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖ ≤ (1 : ℝ) / 2) :
    ‖(sequenceCut target).comp ((H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι).comp
        (sequenceCut source))‖ ≤
      (2 * ‖(H.symm : SequenceL2 ι →L[ℂ] SequenceL2 ι)‖) * Real.exp (-μ * d) :=
  weighted_set_resolvent_bound_of_conjugate_inverse φ μ cap d hμ hφ H source target
    hsource htarget _ (conjugate_inverse_norm_le_two _ H hsmall)

/-- Actual Combes--Thomas estimate for the infinite Yee operator, with
the physical clipped distance and its full source-to-target separation. -/
theorem yee_set_to_set_resolvent
    (H : Lattice.Field ≃L[ℂ] Lattice.Field)
    (m : Lattice.Edge → ℝ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K)
    (hH : (H : Lattice.Field →L[ℂ] Lattice.Field) = Lattice.electricOperator m K hK hm)
    (source target : Set Lattice.Edge) (hsource : source.Nonempty)
    (cap d μ g : ℝ) (hcap : 0 ≤ cap) (hdcap : d ≤ cap) (hμ : 0 ≤ μ) (hg : 0 < g)
    (hsep : ∀ e ∈ target, ∀ f ∈ source, d ≤ siteDistance e.2 f.2)
    (hinv : ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ 1 / g)
    (hsmall : 16 * (Real.exp (2 * μ) - 1) ≤ g / 2) :
    ‖(sequenceCut target).comp ((H.symm : Lattice.Field →L[ℂ] Lattice.Field).comp
        (sequenceCut source))‖ ≤ (2 / g) * Real.exp (-μ * d) := by
  have hconj := clippedDistance_electric_conjugation_norm_le source cap μ hcap hμ m K hK hm
  rw [← hH] at hconj
  have hpert : ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ *
      ‖weightConjugate (exponentialEquiv (clippedDistance source cap) μ cap hμ
        (clippedDistance_bounds source cap hcap)) H -
          (H : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ (1 : ℝ) / 2 := by
    calc
      _ ≤ (1 / g) * (g / 2) := mul_le_mul hinv (hconj.trans hsmall) (norm_nonneg _) (by positivity)
      _ = (1 : ℝ) / 2 := by field_simp
  have h := weighted_set_resolvent_bound (clippedDistance source cap) μ cap d hμ
    (clippedDistance_bounds source cap hcap) H source target
    (clippedDistance_source_zero source cap hcap)
    (fun e he => clippedDistance_target_lower source hsource cap d hdcap e (hsep e he)) hpert
  apply h.trans
  have hi : 2 * ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ 2 / g := by
    calc
      _ ≤ 2 * (1 / g) := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le

@[simp] theorem weightConjugate_id (W : SequenceL2 ι ≃L[ℂ] SequenceL2 ι) :
    weightConjugate W (ContinuousLinearMap.id ℂ (SequenceL2 ι)) =
      ContinuousLinearMap.id ℂ (SequenceL2 ι) := by
  ext f
  simp [weightConjugate]

/-- The shifted inverse and its Combes--Thomas bound are constructed from
the original gap. Charging shift and exponential conjugation together keeps
the manuscript's `2/g` constant; no gap of the shifted operator is assumed. -/
theorem exists_shifted_yee_set_to_set_resolvent
    (H : Lattice.Field ≃L[ℂ] Lattice.Field)
    (m : Lattice.Edge → ℝ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K)
    (hH : (H : Lattice.Field →L[ℂ] Lattice.Field) = Lattice.electricOperator m K hK hm)
    (source target : Set Lattice.Edge) (hsource : source.Nonempty)
    (cap d μ g : ℝ) (hcap : 0 ≤ cap) (hdcap : d ≤ cap) (hμ : 0 ≤ μ) (hg : 0 < g)
    (hsep : ∀ e ∈ target, ∀ f ∈ source, d ≤ siteDistance e.2 f.2)
    (hinv : ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ 1 / g)
    (σ : ℂ) (hσ : ‖σ‖ ≤ g / 4)
    (hsmall : 16 * (Real.exp (2 * μ) - 1) ≤ g / 4) :
    ∃ R : Lattice.Field ≃L[ℂ] Lattice.Field,
      (R : Lattice.Field →L[ℂ] Lattice.Field) =
        (H : Lattice.Field →L[ℂ] Lattice.Field) - σ • ContinuousLinearMap.id ℂ Lattice.Field ∧
      ‖(R.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ 2 / g ∧
      ‖(sequenceCut target).comp ((R.symm : Lattice.Field →L[ℂ] Lattice.Field).comp
        (sequenceCut source))‖ ≤ (2 / g) * Real.exp (-μ * d) := by
  let Δ : Lattice.Field →L[ℂ] Lattice.Field := -(σ • ContinuousLinearMap.id ℂ Lattice.Field)
  have hσmap : ‖σ • ContinuousLinearMap.id ℂ Lattice.Field‖ ≤ ‖σ‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  have hΔ : ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ * ‖Δ‖ ≤ (1 : ℝ) / 4 := by
    calc
      _ ≤ (1 / g) * (g / 4) := by
        apply mul_le_mul hinv _ (norm_nonneg _) (by positivity)
        have hΔnorm : ‖Δ‖ ≤ ‖σ‖ := by simpa only [Δ, norm_neg] using hσmap
        exact hΔnorm.trans hσ
      _ = (1 : ℝ) / 4 := by field_simp
  have hlt : ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ * ‖Δ‖ < 1 := by linarith
  let R := Composition.perturbationEquiv H Δ hlt
  have hR : (R : Lattice.Field →L[ℂ] Lattice.Field) =
      (H : Lattice.Field →L[ℂ] Lattice.Field) - σ • ContinuousLinearMap.id ℂ Lattice.Field := by
    rw [show (R : Lattice.Field →L[ℂ] Lattice.Field) =
      (H : Lattice.Field →L[ℂ] Lattice.Field) + Δ from
        Composition.perturbationEquiv_toContinuousLinearMap H Δ hlt]
    rfl
  have hRdiff : (R : Lattice.Field →L[ℂ] Lattice.Field) -
      (H : Lattice.Field →L[ℂ] Lattice.Field) = Δ := by rw [hR]; dsimp [Δ]; abel
  have hRsmall : ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ *
      ‖(R : Lattice.Field →L[ℂ] Lattice.Field) - (H : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤
        (1 : ℝ) / 2 := by rw [hRdiff]; linarith
  have htwo : 2 * ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ 2 / g := by
    calc
      _ ≤ 2 * (1 / g) := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = _ := by ring
  have hRinv : ‖(R.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ 2 / g :=
    (nearby_inverse_norm_le_two H R hRsmall).trans htwo
  let W := exponentialEquiv (clippedDistance source cap) μ cap hμ
    (clippedDistance_bounds source cap hcap)
  have hconj : ‖weightConjugate W H - (H : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ g / 4 := by
    rw [hH]
    exact (clippedDistance_electric_conjugation_norm_le source cap μ hcap hμ m K hK hm).trans hsmall
  have hconjR : ‖weightConjugate W R - (H : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ g / 2 := by
    rw [hR, weightConjugate_sub, weightConjugate_smul, weightConjugate_id]
    have hid (A B D : Lattice.Field →L[ℂ] Lattice.Field) :
        (A - B) - D = (A - D) - B := by abel
    rw [hid]
    calc
      _ ≤ ‖weightConjugate W H - (H : Lattice.Field →L[ℂ] Lattice.Field)‖ +
          ‖σ • ContinuousLinearMap.id ℂ Lattice.Field‖ := norm_sub_le _ _
      _ ≤ g / 4 + g / 4 := add_le_add hconj (hσmap.trans hσ)
      _ = g / 2 := by ring
  have hcombined : ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ *
      ‖(conjugateEquiv W R : Lattice.Field →L[ℂ] Lattice.Field) -
        (H : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ (1 : ℝ) / 2 := by
    calc
      _ ≤ (1 / g) * (g / 2) := mul_le_mul hinv hconjR (norm_nonneg _) (by positivity)
      _ = (1 : ℝ) / 2 := by field_simp
  have hBinv : ‖((conjugateEquiv W R).symm : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ 2 / g :=
    (nearby_inverse_norm_le_two H (conjugateEquiv W R) hcombined).trans htwo
  refine ⟨R, hR, hRinv, ?_⟩
  exact weighted_set_resolvent_bound_of_conjugate_inverse (clippedDistance source cap) μ cap d hμ
    (clippedDistance_bounds source cap hcap) R source target
    (clippedDistance_source_zero source cap hcap)
    (fun e he => clippedDistance_target_lower source hsource cap d hdcap e (hsep e he))
    (2 / g) hBinv

end Maxwell.Green
