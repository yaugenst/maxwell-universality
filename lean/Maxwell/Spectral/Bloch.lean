import Maxwell.Spectral.Lattice
import Maxwell.Spectral.PeriodicYee
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic.FieldSimp

/-!
# The conventional-cell Fourier transform

The unitary below acts on the actual infinite lattice field. It combines the
integer division-with-remainder bijection with the complete torus Fourier
basis, using the finite Hilbert sum norm on the 24,000 cell components.
-/

namespace Maxwell.Spectral.Bloch

open MeasureTheory
open scoped ENNReal
open Maxwell.Spectral.Lattice

noncomputable section

/-- The conventional cell remainder and the integer cell translate. -/
def intCellEquiv : ℤ ≃ ZMod 20 × ℤ :=
  (Int.divModEquiv 20).trans
    ((Equiv.prodCongr (Equiv.refl ℤ) (ZMod.finEquiv 20).toEquiv).trans (Equiv.prodComm _ _))

def siteCellEquiv : Site ≃ Cell20 × Site where
  toFun x := (fun j => (intCellEquiv (x j)).1, fun j => (intCellEquiv (x j)).2)
  invFun x := fun j => intCellEquiv.symm (x.1 j, x.2 j)
  left_inv x := by funext j; exact intCellEquiv.symm_apply_apply (x j)
  right_inv x := by
    apply Prod.ext <;> funext j <;> simp

def edgeCellEquiv : Edge ≃ Edge20 × Site :=
  (Equiv.prodCongr (Equiv.refl Direction) siteCellEquiv).trans (Equiv.prodAssoc _ _ _).symm


@[simp]
theorem edgeCellEquiv_symm_apply (e : Edge20) (n : Site) :
    edgeCellEquiv.symm (e, n) = (e.1, fun j => n j * 20 + ((e.2 j).val : ℤ)) := rfl

/-- Integer carry at a period-20 boundary. -/
theorem residue_successor (r : ZMod 20) (n : ℤ) :
    n * 20 + (r.val : ℤ) + 1 =
      (n + if r = 19 then 1 else 0) * 20 + ((r + 1).val : ℤ) := by
  have h : ∀ s : ZMod 20, (s.val : ℤ) + 1 =
      (if s = 19 then 1 else 0) * 20 + ((s + 1).val : ℤ) := by decide
  have hs := h r
  omega

def cellForward (j : Direction) (r : Cell20) : Cell20 := r + Pi.single j 1

def cellCarry (j : Direction) (r : Cell20) : Site :=
  if r j = 19 then unitSite j else 0

/-- The full lattice forward step becomes the finite-cell step plus exactly
one integer cell translation at a boundary. -/
theorem reconstructed_forward (r : Cell20) (n : Site) (j : Direction) :
    (fun k => n k * 20 + ((r k).val : ℤ)) + unitSite j =
      (fun k => (n + cellCarry j r) k * 20 + (((cellForward j r) k).val : ℤ)) := by
  funext k
  by_cases hk : k = j
  · subst k
    by_cases hb : r j = 19 <;>
      simpa [unitSite, cellForward, cellCarry, hb] using residue_successor (r j) (n j)
  · by_cases hb : r j = 19 <;> simp [unitSite, cellForward, cellCarry, hk, hb]

/-- Parseval's sum for the standard sequence norm. -/
theorem sequence_norm_sq {ι : Type*} (f : SequenceL2 ι) :
    ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) f

/-- Regrouping a square-summable product index into a finite Hilbert sum. -/
def sequenceCurry {ι κ : Type*} [Fintype ι] :
    SequenceL2 (ι × κ) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : ι => SequenceL2 κ) where
  toFun f := WithLp.toLp 2 fun i => ⟨fun k => f (i, k), by
    apply memℓp_gen
    exact ((lp.memℓp f).summable (by norm_num)).comp_injective
      (fun _ _ h => (Prod.mk.inj h).2)⟩
  invFun f := ⟨fun i => f i.1 i.2, by
    apply memℓp_gen
    apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
    exact ⟨fun i => (lp.memℓp (f i)).summable (by norm_num), (hasSum_fintype _).summable⟩⟩
  left_inv f := by ext i; rfl
  right_inv f := by ext i k; rfl
  map_add' f g := by ext i k; rfl
  map_smul' c f := by ext i k; rfl
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, sequence_norm_sq]
    simp only [sequence_norm_sq]
    change (∑ i, ∑' k, ‖f (i, k)‖ ^ 2) = ∑' i, ‖f i‖ ^ 2
    have hf : Summable (fun i : ι × κ => ‖f i‖ ^ 2) := by
      simpa using (lp.memℓp f).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    simpa only [tsum_fintype] using hf.tsum_prod.symm

@[simp]
theorem sequenceCurry_apply {ι κ : Type*} [Fintype ι]
    (f : SequenceL2 (ι × κ)) (i : ι) (k : κ) :
    sequenceCurry f i k = f (i, k) := rfl

/-- The normalized Haar measure used by mathlib's Fourier Hilbert basis. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

abbrev Torus := UnitAddTorus Direction
abbrev ScalarFiber : Type := Lp ℂ 2 (volume : Measure Torus)
abbrev FiberSpace : Type := PiLp 2 (fun _ : Edge20 => ScalarFiber)

/-- Fourier synthesis with the negative exponential convention, so the
forward lattice shift has the positive Bloch phase. -/
def scalarFourier : SequenceL2 Site ≃ₗᵢ[ℂ] ScalarFiber :=
  (sequenceReindex (Equiv.neg Site)).trans UnitAddTorus.mFourierBasis.repr.symm


/-- Multiplication by an actual torus character on `L²`. -/
def characterMultiplier (a : Site) : ScalarFiber →L[ℂ] ScalarFiber :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 (UnitAddTorus.mFourierLp ∞ a)

theorem characterMultiplier_ae (a : Site) (f : ScalarFiber) :
    characterMultiplier a f =ᵐ[volume] fun t => UnitAddTorus.mFourier a t * f t := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (UnitAddTorus.mFourierLp ∞ a) f (r := 2)
  filter_upwards [h, UnitAddTorus.coeFn_mFourierLp ∞ a] with t ht ha
  change ((ContinuousLinearMap.mul ℂ ℂ).holder 2 (UnitAddTorus.mFourierLp ∞ a) f) t = _
  simpa only [ha, ContinuousLinearMap.mul_apply'] using ht

theorem characterMultiplier_coefficients (a : Site) (f : ScalarFiber) (n : Site) :
    UnitAddTorus.mFourierBasis.repr (characterMultiplier a f) n =
      UnitAddTorus.mFourierBasis.repr f (n - a) := by
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr]
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [characterMultiplier_ae a f] with t ht
  rw [ht]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← UnitAddTorus.mFourier_add]
  rw [neg_sub, sub_eq_add_neg, add_comm (-n) a]

theorem scalarFourier_coefficients (f : SequenceL2 Site) (n : Site) :
    UnitAddTorus.mFourierBasis.repr (scalarFourier f) n = f (-n) := by
  change UnitAddTorus.mFourierBasis.repr
    (UnitAddTorus.mFourierBasis.repr.symm _) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Exact shift/character intertwining for every square-summable sequence. -/
theorem scalarFourier_shift (a : Site) (f : SequenceL2 Site) :
    scalarFourier (sequenceReindex (Equiv.addRight a) f) =
      characterMultiplier a (scalarFourier f) := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext n
  rw [characterMultiplier_coefficients, scalarFourier_coefficients,
    scalarFourier_coefficients, sequenceReindex_apply]
  change f (-n + a) = f (-(n - a))
  rw [neg_sub, sub_eq_add_neg, add_comm]

/-- The infinite-volume conventional-cell Bloch transform. The frequency
variable is normalized to the unit torus; physical phase is `2π t`. -/
def transform : Lattice.Field ≃ₗᵢ[ℂ] FiberSpace :=
  ((sequenceReindex edgeCellEquiv.symm).trans sequenceCurry).trans
    (LinearIsometryEquiv.piLpCongrRight 2 fun _ => scalarFourier)

theorem transform_norm (f : Lattice.Field) : ‖transform f‖ = ‖f‖ :=
  transform.norm_map f

theorem transform_surjective : Function.Surjective transform := transform.surjective

/-- Fourier analysis recovers exactly the original cell-indexed sequence. -/
theorem transform_coefficients (f : Lattice.Field) (e : Edge20) (n : Site) :
    UnitAddTorus.mFourierBasis.repr (transform f e) n = f (edgeCellEquiv.symm (e, -n)) := by
  change UnitAddTorus.mFourierBasis.repr
    (UnitAddTorus.mFourierBasis.repr.symm _) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl


/-- The sequence belonging to a fixed conventional-cell component. -/
def componentSequence (f : Lattice.Field) (e : Edge20) : SequenceL2 Site :=
  sequenceCurry (sequenceReindex edgeCellEquiv.symm f) e

@[simp]
theorem componentSequence_apply (f : Lattice.Field) (e : Edge20) (n : Site) :
    componentSequence f e n = f (edgeCellEquiv.symm (e, n)) := rfl

theorem transform_component (f : Lattice.Field) (e : Edge20) :
    transform f e = scalarFourier (componentSequence f e) := rfl

/-- Each forward stencil term intertwines with the finite-cell shift and its
boundary character. This proves the relation on all of ℓ², without a
finite-support or formal-series assumption. -/
theorem transform_forward_component (p : Equiv.Perm Direction) (j : Direction → Direction)
    (f : Lattice.Field) (d : Direction) (r : Cell20) :
    transform (fieldPullback (fieldPermutation p (fun d => unitSite (j d))) f) (d, r) =
      characterMultiplier (cellCarry (j d) r)
        (transform f (p d, cellForward (j d) r)) := by
  rw [transform_component, transform_component, ← scalarFourier_shift]
  apply congrArg scalarFourier
  ext n
  change f (p d, (fun k => n k * 20 + ((r k).val : ℤ)) + unitSite (j d)) =
    f (p d, fun k => (n + cellCarry (j d) r) k * 20 +
      (((cellForward (j d) r) k).val : ℤ))
  rw [reconstructed_forward]

theorem transform_component_permutation (p : Equiv.Perm Direction)
    (f : Lattice.Field) (d : Direction) (r : Cell20) :
    transform (fieldPullback (fieldPermutation p (fun _ => 0)) f) (d, r) =
      transform f (p d, r) := by
  rw [transform_component, transform_component]
  apply congrArg scalarFourier
  ext n
  change f (p d, (fun k => n k * 20 + ((r k).val : ℤ)) + 0) =
    f (p d, fun k => n k * 20 + ((r k).val : ℤ))
  rw [add_zero]

/-- The exact conventional-cell forward-curl fiber relation. -/
theorem transform_yeeCurl_component (f : Lattice.Field) (d : Direction) (r : Cell20) :
    transform (yeeCurl f) (d, r) =
      characterMultiplier (cellCarry (d + 1) r)
        (transform f (d + 2, cellForward (d + 1) r)) - transform f (d + 2, r) -
      characterMultiplier (cellCarry (d + 2) r)
        (transform f (d + 1, cellForward (d + 2) r)) + transform f (d + 1, r) := by
  simp only [yeeCurl, add_apply, sub_apply,
    map_add, map_sub, PiLp.add_apply, PiLp.sub_apply,
    transform_forward_component, transform_component_permutation]
  rfl


/-- Reconstructing an integer cell translate preserves the finite remainder. -/
theorem edgeMod20_reconstruct (e : Edge20) (n : Site) :
    edgeMod20 (edgeCellEquiv.symm (e, n)) = e := by
  rw [edgeCellEquiv_symm_apply]
  change (e.1, siteMod20 (fun j => n j * 20 + ((e.2 j).val : ℤ))) = e
  refine Prod.ext rfl ?_
  funext j
  change ((n j * 20 + ((e.2 j).val : ℤ) : ℤ) : ZMod 20) = e.2 j
  have hz : (20 : ZMod 20) = 0 := ZMod.natCast_self 20
  simp [Int.cast_add, Int.cast_mul, hz]

/-- Periodic material multiplication transforms to cellwise scalar multiplication. -/
theorem transform_material_component (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (f : Lattice.Field) (e : Edge20) :
    transform (realSequenceMultiplier (periodicCoefficient m) K hK hm f) e =
      (m e : ℂ) • transform f e := by
  rw [transform_component, transform_component, ← map_smul]
  apply congrArg scalarFourier
  ext n
  simp only [componentSequence_apply, realSequenceMultiplier_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, periodicCoefficient, edgeMod20_reconstruct]

/-- A bounded fiber-space operator whose pointwise finite stencil is proved below. -/
def fiberCurl : FiberSpace →L[ℂ] FiberSpace := transform.conjStarAlgEquiv yeeCurl

def fiberMaterial (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K) :
    FiberSpace →L[ℂ] FiberSpace :=
  transform.conjStarAlgEquiv (realSequenceMultiplier (periodicCoefficient m) K hK hm)

theorem fiberCurl_component (f : FiberSpace) (d : Direction) (r : Cell20) :
    fiberCurl f (d, r) =
      characterMultiplier (cellCarry (d + 1) r)
        (f (d + 2, cellForward (d + 1) r)) - f (d + 2, r) -
      characterMultiplier (cellCarry (d + 2) r)
        (f (d + 1, cellForward (d + 2) r)) + f (d + 1, r) := by
  simpa only [fiberCurl, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.apply_symm_apply] using
    transform_yeeCurl_component (transform.symm f) d r

theorem fiberMaterial_component (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (f : FiberSpace) (e : Edge20) :
    fiberMaterial m K hK hm f e = (m e : ℂ) • f e := by
  simpa only [fiberMaterial, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.apply_symm_apply] using
    transform_material_component m K hK hm (transform.symm f) e

/-- The full transformed infinite operator factors as the adjoint fiber curl
square minus the periodic mass, with the actual curl and mass actions above. -/
theorem transform_electricOperator (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K) :
    transform.conjStarAlgEquiv (electricOperator (periodicCoefficient m) K hK hm) =
      fiberCurl.adjoint.comp fiberCurl - (1 / 64 : ℂ) • fiberMaterial m K hK hm := by
  change transform.conjStarAlgEquiv
    (star yeeCurl * yeeCurl - (1 / 64 : ℂ) •
      realSequenceMultiplier (periodicCoefficient m) K hK hm) = _
  simp only [map_sub, map_mul, map_smul, map_star, fiberCurl, fiberMaterial]
  rfl


/-- The boundary character in normalized torus coordinates. -/
def torusPhase (j : Direction) (r : Cell20) (t : Torus) : ℂ :=
  UnitAddTorus.mFourier (cellCarry j r) t

theorem torusPhase_eq (j : Direction) (r : Cell20) (t : Torus) :
    torusPhase j r t = if r j = 19 then fourier 1 (t j) else 1 := by
  by_cases h : r j = 19
  · simp [torusPhase, cellCarry, h, unitSite, UnitAddTorus.mFourier_single]
  · simp [torusPhase, cellCarry, h, UnitAddTorus.mFourier_zero]

/-- The concrete finite matrix symbol of the infinite Yee curl. -/
def torusCurl (t : Torus) : Matrix Edge20 Edge20 ℂ := fun e q =>
  (if q = (e.1 + 2, cellForward (e.1 + 1) e.2) then torusPhase (e.1 + 1) e.2 t else 0) -
  (if q = (e.1 + 2, e.2) then 1 else 0) -
  (if q = (e.1 + 1, cellForward (e.1 + 2) e.2) then torusPhase (e.1 + 2) e.2 t else 0) +
  (if q = (e.1 + 1, e.2) then 1 else 0)

theorem torusCurl_mulVec (t : Torus) (v : Edge20 → ℂ) (d : Direction) (r : Cell20) :
    (torusCurl t).mulVec v (d, r) =
      torusPhase (d + 1) r t * v (d + 2, cellForward (d + 1) r) - v (d + 2, r) -
      torusPhase (d + 2) r t * v (d + 1, cellForward (d + 2) r) + v (d + 1, r) := by
  classical
  simp [Matrix.mulVec, dotProduct, torusCurl, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul]

/-- The transformed curl is pointwise multiplication by its explicit matrix
symbol almost everywhere on the torus. -/
theorem fiberCurl_ae (f : FiberSpace) (e : Edge20) :
    fiberCurl f e =ᵐ[volume] fun t =>
      (torusCurl t).mulVec (fun q => f q t) e := by
  rcases e with ⟨d, r⟩
  rw [fiberCurl_component]
  let a := characterMultiplier (cellCarry (d + 1) r)
    (f (d + 2, cellForward (d + 1) r))
  let b := f (d + 2, r)
  let c := characterMultiplier (cellCarry (d + 2) r)
    (f (d + 1, cellForward (d + 2) r))
  let z := f (d + 1, r)
  filter_upwards [Lp.coeFn_add (a - b - c) z, Lp.coeFn_sub (a - b) c,
    Lp.coeFn_sub a b,
    characterMultiplier_ae (cellCarry (d + 1) r)
      (f (d + 2, cellForward (d + 1) r)),
    characterMultiplier_ae (cellCarry (d + 2) r)
      (f (d + 1, cellForward (d + 2) r))] with t ha hb hc h1 h2
  change (a - b - c + z) t = _
  simp only [Pi.add_apply, Pi.sub_apply] at ha hb hc
  rw [ha, hb, hc]
  change a t - b t - c t + z t = _
  rw [torusCurl_mulVec]
  exact congrArg₂ (fun u v => u - b t - v + z t) h1 h2

theorem fiberMaterial_ae (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (f : FiberSpace) (e : Edge20) :
    fiberMaterial m K hK hm f e =ᵐ[volume] fun t => (m e : ℂ) * f e t := by
  rw [fiberMaterial_component]
  exact Lp.coeFn_smul (m e : ℂ) (f e)


/-- Continuity of every finite matrix entry, including across the torus seams. -/
theorem torusCurl_continuous : Continuous torusCurl := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro q
  unfold torusCurl torusPhase
  split_ifs <;> fun_prop

/-- Physical momentum in radians, modulo the conventional Brillouin period. -/
def momentumTorus (k : PeriodicYee.Momentum) : Torus :=
  fun j => ((k j / (2 * Real.pi) : ℝ) : UnitAddCircle)

theorem momentumTorus_surjective : Function.Surjective momentumTorus := by
  intro t
  refine ⟨fun j => (2 * Real.pi) * (AddCircle.equivIoc 1 0 (t j)).val, ?_⟩
  funext j
  simp [momentumTorus, Real.pi_ne_zero]

theorem torusPhase_momentum (k : PeriodicYee.Momentum) (j : Direction) (r : Cell20) :
    torusPhase j r (momentumTorus k) = PeriodicYee.boundaryPhase k j r := by
  rw [torusPhase_eq]
  unfold PeriodicYee.boundaryPhase
  split_ifs
  · change fourier 1 ((k j / (2 * Real.pi) : ℝ) : UnitAddCircle) = _
    rw [fourier_coe_apply]
    congr 1
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  · rfl

/-- Exact agreement with the conventional period-20 matrix already used by
the finite certificate; this fixes the Bloch gauge and all boundary signs. -/
theorem torusCurl_eq_periodic (k : PeriodicYee.Momentum) :
    torusCurl (momentumTorus k) = PeriodicYee.curl k := by
  ext ⟨d, r⟩ ⟨j, s⟩
  fin_cases d <;> fin_cases j <;>
    simp [torusCurl, PeriodicYee.curl, PeriodicYee.difference, torusPhase_momentum,
      cellForward, PeriodicYee.forwardCell, PeriodicYee.unitCell, Prod.mk.injEq]
  all_goals simp_all [PeriodicYee.boundaryPhase, sub_eq_add_neg, add_comm]
  all_goals rfl


/-- The continuous finite electric symbol for a cellwise edge mass. -/
def torusElectric (m : Edge20 → ℝ) (t : Torus) : Matrix Edge20 Edge20 ℂ :=
  (torusCurl t).conjTranspose * torusCurl t -
    (1 / 64 : ℂ) • Matrix.diagonal (fun e => (m e : ℂ))

theorem torusElectric_continuous (m : Edge20 → ℝ) : Continuous (torusElectric m) :=
  (torusCurl_continuous.matrix_conjTranspose.mul torusCurl_continuous).sub continuous_const

theorem torusElectric_hermitian (m : Edge20 → ℝ) (t : Torus) :
    (torusElectric m t).IsHermitian := by
  apply (Matrix.isHermitian_conjTranspose_mul_self (torusCurl t)).sub
  have hm : (Matrix.diagonal (fun e => (m e : ℂ))).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext e; simp)
  exact hm.smul (by simp)

/-- The actual infinite mass is the periodic extension of the paper's
four-incident-cell edge average. Its finite symbol is exactly the previously
defined conventional-cell fiber. -/
theorem torusElectric_eq_periodic (material : PeriodicYee.Cell20 → ℝ)
    (k : PeriodicYee.Momentum) :
    torusElectric (PeriodicYee.edgeAverage material) (momentumTorus k) =
      PeriodicYee.fiber material k := by
  unfold torusElectric PeriodicYee.fiber PeriodicYee.mass
  rw [torusCurl_eq_periodic]

end

end Maxwell.Spectral.Bloch
