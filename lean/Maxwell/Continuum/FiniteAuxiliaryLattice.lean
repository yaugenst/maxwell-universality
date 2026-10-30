import Maxwell.Continuum.FiniteAuxiliaryTranslation
import Maxwell.Continuum.UsefulCoupling
import Maxwell.Composition.Lattice

/-! The literal finite placement lattice: displacements, injectivity,
and transfer of the certified whole-lattice geometric row sums. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Bloch CellGauge EffectiveMass PeriodicBand Auxiliary MasterConstants

def aliasTriple (a : Bloch.Alias) : Composition.Lattice3 := (a 0,a 1,a 2)

theorem aliasTriple_injective : Function.Injective aliasTriple := by
  intro a b hab
  have h0 := congrArg Prod.fst hab
  have h1 := congrArg (fun x : Composition.Lattice3 => x.2.1) hab
  have h2 := congrArg (fun x : Composition.Lattice3 => x.2.2) hab
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

theorem aliasTriple_zero : aliasTriple (0 : Bloch.Alias) = (0,0,0) := rfl

theorem aliasTriple_distance (a : Bloch.Alias) :
    Composition.latticeDistance (aliasTriple a) = latticeOneNorm a := by
  simp only [aliasTriple, Composition.latticeDistance, latticeOneNorm, Fin.sum_univ_three]

theorem aliasTriple_weight (ζ : ℝ) (a : Bloch.Alias) :
    Composition.latticeWeight ζ (aliasTriple a) = ζ^latticeOneNorm a := by
  rw [Composition.latticeWeight, aliasTriple_distance]

theorem placementCell_sub (L d : ℕ) (a b : Bloch.Alias) :
    placementCell L d (a-b) = placementCell L d a-placementCell L d b := by
  funext j
  simp only [placementCell, Matrix.mulVec_sub, Pi.sub_apply, mul_sub]

def centers {ι : Type*} (L d : ℕ) (position : ι → Bloch.Alias) : ι → Space :=
  fun i => latticeShift (placementCell L d (position i))

theorem centers_sub {ι : Type*} (L d : ℕ) (position : ι → Bloch.Alias) (i j : ι) :
    centers L d position i-centers L d position j =
      latticeShift (placementCell L d (position i-position j)) := by
  rw [placementCell_sub, latticeShift_sub]
  rfl

theorem centers_interaction {ι : Type*} {L : ℕ} {z σ : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (position : ι → Bloch.Alias) (i j : ι) :
    (siteRestriction (L : ℝ)⁻¹ (centers L d position i)).comp
      ((resolvent D hσ0 hσ).comp (siteInsertion (L : ℝ)⁻¹ (centers L d position j))) =
      physicalWellBlock D hσ0 hσ d (position i-position j) := by
  rw [centers, centers, site_interaction_eq, physicalWellBlock, ← placementCell_neg,
    neg_sub, placementCell_sub]

theorem occupied_nonzero_weight {ι : Type*} (position : ι → Bloch.Alias)
    (hinj : Function.Injective position) (s : Finset ι) {ζ : ℝ}
    (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1/2) (h0 : ∀ i ∈ s, position i ≠ 0) :
    ∑ i ∈ s, ζ^latticeOneNorm (position i) ≤ 64*ζ := by
  classical
  let p := aliasTriple ∘ position
  have hp : Function.Injective p := aliasTriple_injective.comp hinj
  have hz : (0,0,0) ∉ s.image p := by
    intro hz
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hz
    apply h0 i hi
    exact aliasTriple_injective (he.trans aliasTriple_zero.symm)
  have he := Composition.lattice_nonzero_sum_bound ζ hζ hhalf (s.image p) hz
  rw [Finset.sum_image (fun i _ j _ hij => hp hij)] at he
  simpa only [p, Function.comp_apply, aliasTriple_weight] using he

theorem occupied_far_weight {ι : Type*} (position : ι → Bloch.Alias)
    (hinj : Function.Injective position) (s : Finset ι) {ζ : ℝ}
    (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1/2) (hfar : ∀ i ∈ s, 2 ≤ latticeOneNorm (position i)) :
    ∑ i ∈ s, ζ^latticeOneNorm (position i) ≤ 256*ζ^2 := by
  have he := Composition.occupied_far_weight_bound (aliasTriple ∘ position)
    (aliasTriple_injective.comp hinj) s ζ hζ hhalf (by
      intro i hi
      simpa only [Function.comp_apply, aliasTriple_distance] using hfar i hi)
  simpa only [Function.comp_apply, aliasTriple_weight] using he

theorem physicalWellBlock_geometric {L : ℕ} {z σ : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (a : Bloch.Alias) :
    ‖physicalWellBlock D hσ0 hσ d a‖ ≤
      Cs*(L : ℝ)^5*(((3 : ℝ)^d)⁻¹^latticeOneNorm a+Real.exp (-cs*(L : ℝ))) := by
  simpa only [pow_mul, inv_pow] using physicalWellBlock_norm hL D hσ0 hσ d a

#print axioms centers_interaction
#print axioms occupied_nonzero_weight
#print axioms occupied_far_weight

end Maxwell.Continuum.FiniteAuxiliary
