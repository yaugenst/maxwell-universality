import Maxwell.Green.PhysicalCompression
import Mathlib.Algebra.Group.Commute.Units

/-! Actual cell-translation covariance of the periodic infinite Yee
operator and its inverse, and the resulting equality of translated defect
blocks with the single-prototype Green compression. -/

noncomputable section
namespace Maxwell.Composition.TranslationBlocks

open Maxwell.Spectral Maxwell.Spectral.Lattice
open Maxwell.Green.PhysicalCompression

/-- Pullback by minus a cell displacement translates a supported field by
plus that displacement. -/
def shiftIndex (n : Site) : Equiv.Perm Edge :=
  fieldPermutation (Equiv.refl _) (fun _ => -(20 • n))

def shift (n : Site) : Field →L[ℂ] Field := fieldPullback (shiftIndex n)

@[simp] theorem shift_apply (n : Site) (f : Field) (e : Edge) :
    shift n f e = f (e.1, e.2 - 20 • n) := by
  change f (e.1, e.2 + -(20 • n)) = _
  rw [sub_eq_add_neg]

@[simp] theorem shift_zero : shift 0 = 1 := by
  ext f e
  simp

theorem shift_mul (a b : Site) : shift a * shift b = shift (a + b) := by
  ext f e
  change f (e.1, (e.2 - 20 • a) - 20 • b) = f (e.1, e.2 - 20 • (a + b))
  apply congrArg f
  exact congrArg (fun x : Site => (e.1, x)) (by simp only [smul_add]; abel)

@[simp] theorem shift_adjoint (n : Site) : (shift n).adjoint = shift (-n) := by
  have h := (sequenceReindex (shiftIndex n)).adjoint_eq_symm
  change (shift n).adjoint = _ at h
  rw [h]
  ext f e
  change f (e.1, e.2 - -(20 • n)) = f (e.1, e.2 - 20 • -n)
  rw [smul_neg]

theorem shift_commutes_pullback (n : Site) (p : Equiv.Perm Direction)
    (v : Direction → Site) : Commute (shift n) (fieldPullback (fieldPermutation p v)) := by
  ext f e
  change f (p e.1, (e.2 - 20 • n) + v e.1) =
    f (p e.1, (e.2 + v e.1) - 20 • n)
  apply congrArg f
  exact congrArg (fun x : Site => (p e.1, x)) (by abel)

theorem shift_commutes_curl (n : Site) : Commute (shift n) yeeCurl := by
  unfold yeeCurl
  exact ((shift_commutes_pullback n _ _).sub_right (shift_commutes_pullback n _ _)).sub_right
    (shift_commutes_pullback n _ _) |>.add_right (shift_commutes_pullback n _ _)

theorem shift_commutes_curl_adjoint (n : Site) : Commute (shift n) yeeCurl.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (shift_commutes_curl (-n)).eq
  change (shift n).comp yeeCurl.adjoint = yeeCurl.adjoint.comp (shift n)
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    shift_adjoint, neg_neg] using h.symm

theorem periodicCoefficient_sub (m : Edge20 → ℝ) (d : Direction) (x n : Site) :
    periodicCoefficient m (d, x - 20 • n) = periodicCoefficient m (d, x) := by
  simpa only [smul_neg, sub_eq_add_neg] using periodicCoefficient_periodic m d x (-n)

theorem shift_commutes_mass (n : Site) (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K) :
    Commute (shift n) (realSequenceMultiplier (periodicCoefficient m) K hK hm) := by
  ext f e
  simp only [mul_apply_eq_comp, shift_apply, realSequenceMultiplier_apply,
    periodicCoefficient_sub]

/-- Translation covariance follows from the actual four-term Yee curl and
the actual period-twenty material multiplier. -/
theorem shift_commutes_electric (n : Site) (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K) :
    Commute (shift n) (electricOperator (periodicCoefficient m) K hK hm) := by
  have hc := (shift_commutes_curl_adjoint n).mul_right (shift_commutes_curl n)
  have hm' := shift_commutes_mass n m K hK hm
  change shift n * (yeeCurl.adjoint * yeeCurl -
    (1 / 64 : ℂ) • realSequenceMultiplier (periodicCoefficient m) K hK hm) =
      (yeeCurl.adjoint * yeeCurl -
        (1 / 64 : ℂ) • realSequenceMultiplier (periodicCoefficient m) K hK hm) * shift n
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hc.eq, hm'.eq]

theorem shift_commutes_shifted_electric (n : Site) (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℂ) :
    Commute (shift n) (electricOperator (periodicCoefficient m) K hK hm - z • 1) := by
  have h := shift_commutes_electric n m K hK hm
  change shift n * (_ - z • 1) = (_ - z • 1) * shift n
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, h.eq]

theorem commute_ringInverse (A B : Field →L[ℂ] Field) (h : Commute A B) :
    Commute A (Ring.inverse B) := by
  by_cases hB : IsUnit B
  · rcases hB with ⟨u, rfl⟩
    simpa only [Ring.inverse_unit] using h.units_inv_right
  · rw [Ring.inverse_non_unit _ hB]
    exact Commute.zero_right _

/-- This is covariance of the actual inverse, not an independent
translation-invariant Green function hypothesis. -/
theorem shift_commutes_inverse (n : Site) (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℂ) :
    Commute (shift n)
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - z • 1)) :=
  commute_ringInverse _ _ (shift_commutes_shifted_electric n m K hK hm z)

variable {N : ℕ}

/-- The prototype edges physically placed at plus twenty times an anchor. -/
def placedEmbedding (edges : Fin N ↪ Edge) (anchor : Site) : Fin N ↪ Edge :=
  translatedEmbedding edges (-anchor)

@[simp] theorem placedEmbedding_apply (edges : Fin N ↪ Edge) (anchor : Site) (i : Fin N) :
    placedEmbedding edges anchor i = ((edges i).1, (edges i).2 + 20 • anchor) := by
  simp [placedEmbedding, translatedEmbedding, translateEdge]

theorem extension_placed (edges : Fin N ↪ Edge) (anchor : Site) :
    (Maxwell.Target.sequenceExtension (placedEmbedding edges anchor)).toContinuousLinearMap =
      (shift anchor).comp (Maxwell.Target.sequenceExtension edges).toContinuousLinearMap := by
  ext x e
  change Maxwell.Target.sequenceExtensionLinear (placedEmbedding edges anchor) x e =
    Maxwell.Target.sequenceExtensionLinear edges x (e.1, e.2 - 20 • anchor)
  rw [Maxwell.Target.sequenceExtensionLinear_apply, Maxwell.Target.sequenceExtensionLinear_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [placedEmbedding_apply]
  exact propext (by simp only [Prod.ext_iff, sub_eq_iff_eq_add])

theorem injection_placed (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (anchor : Site) :
    Maxwell.Defect.defectInjection (placedEmbedding edges anchor) W =
      (shift anchor).comp (Maxwell.Defect.defectInjection edges W) := by
  rw [Maxwell.Defect.defectInjection, extension_placed]
  rfl

/-- The two distinct physical placements of the same weighted prototype. -/
def placedBlock (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (T : Field →L[ℂ] Field)
    (a b : Site) : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (Maxwell.Defect.defectInjection (placedEmbedding edges a) W).adjoint.comp
    (T.comp (Maxwell.Defect.defectInjection (placedEmbedding edges b) W))

theorem placedBlock_eq_weightedBlock (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (T : Field →L[ℂ] Field) (hT : ∀ n, Commute (shift n) T) (a b : Site) :
    placedBlock edges W T a b = weightedBlock edges W T (a - b) := by
  have he : translatedEmbedding edges (a - b) = placedEmbedding edges (b - a) := by
    unfold placedEmbedding
    congr 1
    abel
  unfold placedBlock weightedBlock
  rw [he, injection_placed, injection_placed, injection_placed,
    ContinuousLinearMap.adjoint_comp, shift_adjoint]
  have h : (shift (-a)).comp (T.comp (shift b)) = T.comp (shift (b - a)) := by
    change shift (-a) * (T * shift b) = T * shift (b - a)
    rw [← mul_assoc, (hT (-a)).eq, mul_assoc, shift_mul]
    congr 2
    abel
  simpa only [ContinuousLinearMap.comp_assoc] using
    congrArg (fun X : Field →L[ℂ] Field =>
      (Maxwell.Defect.defectInjection edges W).adjoint.comp
        (X.comp (Maxwell.Defect.defectInjection edges W))) h

/-- Exact identification of the actual periodic inverse block at two
positive anchor placements with the prototype block at their difference. -/
theorem inverse_placedBlock (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℂ) (a b : Site) :
    placedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - z • 1)) a b =
    weightedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - z • 1)) (a - b) :=
  placedBlock_eq_weightedBlock edges W _ (fun n => shift_commutes_inverse n m K hK hm z) a b

end Maxwell.Composition.TranslationBlocks
