import Maxwell.Spectral.Perturbation
import Mathlib.Data.Fintype.EquivFin

/-!
# Counting every zero crossing of a finite Hermitian Schur family

The common scalar decrease gives injectivity of each ordered eigenvalue's
zero set. Consequently the total crossing multiplicity, rather than just
the number of distinct crossing locations, is bounded by the dimension.
This uses the existing generic finite-dimensional min--max theorem only.
-/

noncomputable section

namespace Maxwell.Continuum.MonotoneCrossing

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

variable (A : ℝ → H →ₗ[ℂ] H) (hA : ∀ t, (A t).IsSymmetric) (W : Set ℝ)
variable (hmono : ∀ a ∈ W, ∀ b ∈ W, a ≤ b → ∀ x : H,
  (inner ℂ x (A b x)).re ≤ (inner ℂ x (A a x)).re - (b - a) * ‖x‖ ^ 2)

def eigenvalue (t : ℝ) (i : Fin (Module.finrank ℂ H)) : ℝ :=
  (hA t).eigenvalues rfl i

include hmono in
theorem eigenvalue_decrease {a b : ℝ} (ha : a ∈ W) (hb : b ∈ W) (hab : a ≤ b)
    (i : Fin (Module.finrank ℂ H)) :
    eigenvalue A hA b i ≤ eigenvalue A hA a i - (b - a) := by
  apply Maxwell.Spectral.eigenvalues_le_of_quadratic_le_add (hA b) (hA a) (-(b - a))
  intro x
  simpa only [neg_mul, sub_eq_add_neg] using hmono a ha b hb hab x

include hmono in
theorem eigenvalue_strictAnti (i : Fin (Module.finrank ℂ H)) :
    StrictAntiOn (fun t => eigenvalue A hA t i) W := by
  intro a ha b hb hab
  have h := eigenvalue_decrease A hA W hmono ha hb hab.le i
  linarith

include hmono in
theorem zero_unique (i : Fin (Module.finrank ℂ H)) {a b : ℝ}
    (ha : a ∈ W) (hb : b ∈ W)
    (hza : eigenvalue A hA a i = 0) (hzb : eigenvalue A hA b i = 0) : a = b :=
  (eigenvalue_strictAnti A hA W hmono i).injOn ha hb (hza.trans hzb.symm)

def zeroSet : Set ℝ := {t | t ∈ W ∧ ∃ i, eigenvalue A hA t i = 0}

/-- The chosen zero index embeds all distinct singular parameters into the
finite set of ordered eigenvalue labels. -/
def zeroIndex (t : zeroSet A hA W) : Fin (Module.finrank ℂ H) :=
  t.property.2.choose

theorem zeroIndex_spec (t : zeroSet A hA W) :
    eigenvalue A hA t (zeroIndex A hA W t) = 0 := t.property.2.choose_spec

include hmono in
theorem zeroIndex_injective : Function.Injective (zeroIndex A hA W) := by
  intro a b hab
  apply Subtype.ext
  apply zero_unique A hA W hmono (zeroIndex A hA W a) a.property.1 b.property.1
    (zeroIndex_spec A hA W a)
  rw [hab]
  exact zeroIndex_spec A hA W b

include hmono in
theorem zeroSet_finite : (zeroSet A hA W).Finite := by
  have : Finite (zeroSet A hA W) :=
    Finite.of_injective (zeroIndex A hA W) (zeroIndex_injective A hA W hmono)
  exact Set.toFinite _

def zeroFinset : Finset ℝ := (zeroSet_finite A hA W hmono).toFinset

@[simp] theorem mem_zeroFinset (t : ℝ) :
    t ∈ zeroFinset A hA W hmono ↔ t ∈ W ∧ ∃ i, eigenvalue A hA t i = 0 := by
  simp only [zeroFinset, Set.Finite.mem_toFinset, zeroSet, Set.mem_ofPred_eq]

theorem zeroFinset_card_le :
    (zeroFinset A hA W hmono).card ≤ Module.finrank ℂ H := by
  classical
  let := (zeroSet_finite A hA W hmono).fintype
  have h := Fintype.card_le_of_injective _ (zeroIndex_injective A hA W hmono)
  simpa only [Fintype.card_fin, zeroFinset, Set.Finite.card_toFinset] using h

include hmono in
/-- Every eigenvalue label can contribute at only one parameter, so repeated
roots at one parameter are counted with their full multiplicity. -/
theorem sum_zero_multiplicities_le (s : Finset ℝ) (hs : ∀ t ∈ s, t ∈ W) :
    (∑ t ∈ s, (Finset.univ.filter fun i => eigenvalue A hA t i = 0).card) ≤
      Module.finrank ℂ H := by
  classical
  let labels (t : ℝ) := Finset.univ.filter fun i => eigenvalue A hA t i = 0
  have hd : (s : Set ℝ).PairwiseDisjoint labels := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hab (zero_unique A hA W hmono i (hs a ha) (hs b hb)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
  calc
    _ = (s.biUnion labels).card := (Finset.card_biUnion hd).symm
    _ ≤ Fintype.card (Fin (Module.finrank ℂ H)) := Finset.card_le_univ _
    _ = _ := Fintype.card_fin _

theorem zero_multiplicity_eq_kernel (t : ℝ) :
    (Finset.univ.filter fun i => eigenvalue A hA t i = 0).card =
      Module.finrank ℂ (A t).ker := by
  classical
  rw [← Module.End.eigenspace_zero (A t)]
  simpa [eigenvalue] using
    (hA t).card_filter_eigenvalues_eq rfl (0 : ℂ)

include hA hmono in
theorem sum_kernel_dimensions_le (s : Finset ℝ) (hs : ∀ t ∈ s, t ∈ W) :
    (∑ t ∈ s, Module.finrank ℂ (A t).ker) ≤ Module.finrank ℂ H := by
  simp_rw [← zero_multiplicity_eq_kernel A hA]
  exact sum_zero_multiplicities_le A hA W hmono s hs

theorem exists_zero_iff_kernel (t : ℝ) :
    (∃ i, eigenvalue A hA t i = 0) ↔ (A t).ker ≠ ⊥ := by
  classical
  have hc : (∃ i, eigenvalue A hA t i = 0) ↔
      (Finset.univ.filter fun i => eigenvalue A hA t i = 0).card ≠ 0 := by simp
  exact hc.trans ((congrArg (fun n : ℕ => n ≠ 0)
    (zero_multiplicity_eq_kernel A hA t)).to_iff.trans
      (not_congr (Submodule.finrank_eq_zero (R := ℂ) (S := (A t).ker))))

@[simp] theorem mem_zeroFinset_iff_kernel (t : ℝ) :
    t ∈ zeroFinset A hA W hmono ↔ t ∈ W ∧ (A t).ker ≠ ⊥ := by
  rw [mem_zeroFinset, exists_zero_iff_kernel]

end Maxwell.Continuum.MonotoneCrossing
