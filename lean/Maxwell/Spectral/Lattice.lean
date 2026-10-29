import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Bounded operators on the infinite Yee lattice

The field space is the standard Hilbert space of square-summable complex
sequences. Coordinate permutations act unitarily, real bounded material
coefficients act by a self-adjoint multiplier, and the forward Yee curl is
a sum of four coordinate permutations.
-/

namespace Maxwell.Spectral

noncomputable section

abbrev SequenceL2 (ι : Type*) : Type _ := lp (fun _ : ι => ℂ) 2

/-- Pullback of square-summable sequences along an index equivalence. -/
def sequenceReindex {ι κ : Type*} (e : ι ≃ κ) : SequenceL2 κ ≃ₗᵢ[ℂ] SequenceL2 ι where
  toFun f := ⟨fun i => f (e i), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  invFun f := ⟨fun i => f (e.symm i), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' f g := by ext i; rfl
  map_smul' c f := by ext i; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun i : κ => ‖f i‖ ^ (2 : ENNReal).toReal)

@[simp]
theorem sequenceReindex_apply {ι κ : Type*} (e : ι ≃ κ) (f : SequenceL2 κ) (i : ι) :
    sequenceReindex e f i = f (e i) := rfl

/-- Multiplication by a bounded real sequence, as a bounded complex-linear map. -/
def realSequenceMultiplier {ι : Type*} (m : ι → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K) : SequenceL2 ι →L[ℂ] SequenceL2 ι :=
  lp.mapCLM 2 (fun i => (m i : ℂ) • ContinuousLinearMap.id ℂ ℂ) hK (by
    intro i
    simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one, Complex.norm_real,
      Real.norm_eq_abs] using hm i)

@[simp]
theorem realSequenceMultiplier_apply {ι : Type*} (m : ι → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K) (f : SequenceL2 ι) (i : ι) :
    realSequenceMultiplier m K hK hm f i = (m i : ℂ) * f i := rfl

theorem realSequenceMultiplier_norm_le {ι : Type*} (m : ι → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K) :
    ‖realSequenceMultiplier m K hK hm‖ ≤ K :=
  lp.norm_mapCLM_le 2 _ hK _

/-- Real pointwise material multiplication is self-adjoint on the actual
infinite-dimensional Hilbert space. -/
theorem realSequenceMultiplier_selfAdjoint {ι : Type*} (m : ι → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K) :
    IsSelfAdjoint (realSequenceMultiplier m K hK hm) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  change inner ℂ ((m i : ℂ) • x i) (y i) = inner ℂ (x i) ((m i : ℂ) • y i)
  simp only [inner_smul_left, inner_smul_right]
  simp


namespace Lattice

abbrev Direction := Fin 3
abbrev Site := Direction → ℤ
abbrev Edge := Direction × Site
abbrev Field : Type := SequenceL2 Edge

def unitSite (j : Direction) : Site := Pi.single j 1

abbrev Cell20 := Direction → ZMod 20
abbrev Edge20 := Direction × Cell20

/-- Reduction of an integer site modulo the conventional period. -/
def siteMod20 (x : Site) : Cell20 := fun j => (x j : ZMod 20)

def edgeMod20 (e : Edge) : Edge20 := (e.1, siteMod20 e.2)

def periodicCoefficient (m : Edge20 → ℝ) (e : Edge) : ℝ := m (edgeMod20 e)

theorem siteMod20_periodic (x v : Site) : siteMod20 (x + 20 • v) = siteMod20 x := by
  ext j
  simp [siteMod20]
  have hz : (20 : ZMod 20) = 0 := ZMod.natCast_self 20
  rw [hz, zero_mul]

theorem periodicCoefficient_periodic (m : Edge20 → ℝ) (d : Direction) (x v : Site) :
    periodicCoefficient m (d, x + 20 • v) = periodicCoefficient m (d, x) := by
  simp only [periodicCoefficient, edgeMod20, siteMod20_periodic]

theorem periodicCoefficient_bound (m : Edge20 → ℝ) (K : ℝ)
    (hm : ∀ e, |m e| ≤ K) (e : Edge) : |periodicCoefficient m e| ≤ K :=
  hm (edgeMod20 e)

/-- Cyclic coordinate orientation `(x,y,z)`. -/
def directionCycle : Equiv.Perm Direction where
  toFun d := d + 1
  invFun d := d + 2
  left_inv d := by fin_cases d <;> rfl
  right_inv d := by fin_cases d <;> rfl

/-- Permuting components and shifting each component by a fixed integer vector
is a bijection of the complete infinite field index set. -/
def fieldPermutation (p : Equiv.Perm Direction) (v : Direction → Site) :
    Equiv.Perm Edge where
  toFun e := (p e.1, e.2 + v e.1)
  invFun e := (p.symm e.1, e.2 - v (p.symm e.1))
  left_inv e := by simp
  right_inv e := by simp

def fieldPullback (e : Equiv.Perm Edge) : Field →L[ℂ] Field :=
  (sequenceReindex e).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem fieldPullback_apply (e : Equiv.Perm Edge) (f : Field) (i : Edge) :
    fieldPullback e f i = f (e i) := rfl

/-- The forward-difference Yee curl, with unit lattice spacing. -/
def yeeCurl : Field →L[ℂ] Field :=
  fieldPullback (fieldPermutation directionCycle.symm (fun d => unitSite (d + 1))) -
  fieldPullback (fieldPermutation directionCycle.symm (fun _ => 0)) -
  fieldPullback (fieldPermutation directionCycle (fun d => unitSite (d + 2))) +
  fieldPullback (fieldPermutation directionCycle (fun _ => 0))

/-- Exact pointwise stencil on every integer lattice site. -/
theorem yeeCurl_apply (f : Field) (d : Direction) (x : Site) :
    yeeCurl f (d, x) =
      f (d + 2, x + unitSite (d + 1)) - f (d + 2, x) -
      f (d + 1, x + unitSite (d + 2)) + f (d + 1, x) := by
  simp [yeeCurl, fieldPullback, fieldPermutation, directionCycle]

theorem fieldPullback_norm_le (e : Equiv.Perm Edge) : ‖fieldPullback e‖ ≤ 1 :=
  (sequenceReindex e).toLinearIsometry.norm_toContinuousLinearMap_le

/-- A uniform infinite-volume operator norm bound follows directly from the
four isometric coordinate pullbacks. -/
theorem yeeCurl_norm_le : ‖yeeCurl‖ ≤ 4 := by
  unfold yeeCurl
  calc
    _ ≤ ((‖fieldPullback (fieldPermutation directionCycle.symm
        (fun d => unitSite (d + 1)))‖ +
      ‖fieldPullback (fieldPermutation directionCycle.symm (fun _ => 0))‖) +
      ‖fieldPullback (fieldPermutation directionCycle (fun d => unitSite (d + 2)))‖) +
      ‖fieldPullback (fieldPermutation directionCycle (fun _ => 0))‖ := by
        grw [norm_add_le, norm_sub_le, norm_sub_le]
    _ ≤ 4 := by
      linarith [fieldPullback_norm_le (fieldPermutation directionCycle.symm
        (fun d => unitSite (d + 1))),
        fieldPullback_norm_le (fieldPermutation directionCycle.symm (fun _ => 0)),
        fieldPullback_norm_le (fieldPermutation directionCycle (fun d => unitSite (d + 2))),
        fieldPullback_norm_le (fieldPermutation directionCycle (fun _ => 0))]

/-- The infinite electric-field operator at frequency `omega=1/8`. -/
def electricOperator (m : Edge → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K) : Field →L[ℂ] Field :=
  yeeCurl.adjoint.comp yeeCurl - (1 / 64 : ℂ) • realSequenceMultiplier m K hK hm

/-- The full infinite-lattice electric operator is bounded and self-adjoint. -/
theorem electricOperator_selfAdjoint (m : Edge → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K) :
    IsSelfAdjoint (electricOperator m K hK hm) := by
  unfold electricOperator
  have hD : IsSelfAdjoint ((1 / 64 : ℂ) • realSequenceMultiplier m K hK hm) :=
    (show IsSelfAdjoint (1 / 64 : ℂ) by simp [IsSelfAdjoint]).smul
      (realSequenceMultiplier_selfAdjoint m K hK hm)
  have hC : IsSelfAdjoint (yeeCurl.adjoint.comp yeeCurl) := IsSelfAdjoint.star_mul_self yeeCurl
  exact IsSelfAdjoint.sub (R := Field →L[ℂ] Field) hC hD

end Lattice

end

end Maxwell.Spectral
