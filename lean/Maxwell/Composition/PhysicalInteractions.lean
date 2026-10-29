import Maxwell.Composition.PeriodicBackground

/-! Complete off-diagonal and non-incidence interaction bounds for the
actual decorated physical set, with no defect-count multiplier. -/
noncomputable section
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice
open scoped BigOperators

theorem occupied_nonzero_row_bound {ι : Type*} [Fintype ι]
    (position : ι → Lattice3) (hinj : Function.Injective position)
    (weight : ι → ℝ) (C ζ : ℝ) (hC : 0 ≤ C) (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1 / 2)
    (hzero : ∀ i, position i = 0 → weight i = 0)
    (hweight : ∀ i, weight i ≤ C * latticeWeight ζ (position i)) :
    ∑ i, weight i ≤ C * (64 * ζ) := by
  classical
  let s := Finset.univ.filter fun i => position i ≠ 0
  have hs : ∑ i, weight i = ∑ i ∈ s, weight i := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : position i = 0
    · simp [hi, hzero i hi]
    · simp [hi]
  have hz : (0 : Lattice3) ∉ s.image position := by
    intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hi).2 he
  have hw := lattice_nonzero_sum_bound ζ hζ hhalf (s.image position) hz
  rw [Finset.sum_image (fun i _ j _ hij => hinj hij)] at hw
  calc
    _ = ∑ i ∈ s, weight i := hs
    _ ≤ ∑ i ∈ s, C * latticeWeight ζ (position i) := Finset.sum_le_sum fun i _ => hweight i
    _ = C * ∑ i ∈ s, latticeWeight ζ (position i) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (64 * ζ) := mul_le_mul_of_nonneg_left hw hC

theorem lattice_offdiag_operator_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (position : ι → Lattice3) (hinj : Function.Injective position)
    (C ζ : ℝ) (hC : 0 ≤ C) (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1 / 2)
    (hdiag : ∀ i, A i i = 0)
    (hdecay : ∀ i j, ‖A i j‖ ≤ C * latticeWeight ζ (position j - position i)) :
    ‖interactionOperator A‖ ≤ 64 * C * ζ := by
  have hrow : ∀ i, ∑ j, ‖A i j‖ ≤ C * (64 * ζ) := by
    intro i
    apply occupied_nonzero_row_bound (fun j => position j - position i)
      (fun a b h => hinj (sub_left_inj.mp h)) (fun j => ‖A i j‖) C ζ hC hζ hhalf
    · intro j hj
      have he := hinj (sub_eq_zero.mp hj)
      subst j
      rw [hdiag, norm_zero]
    · exact hdecay i
  have hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C * (64 * ζ) := by
    intro j
    apply occupied_nonzero_row_bound (fun i => position j - position i)
      (fun a b h => hinj (sub_right_inj.mp h)) (fun i => ‖A i j‖) C ζ hC hζ hhalf
    · intro i hi
      have he := hinj (sub_eq_zero.mp hi)
      subst j
      rw [hdiag, norm_zero]
    · intro i; exact hdecay i j
  exact (interaction_operator_norm_le A (C * (64 * ζ)) (by positivity) hrow hcol).trans_eq (by ring)

namespace PhysicalInteractions

def siteTriple (x : Site) : Lattice3 := (x 0, x 1, x 2)

theorem siteTriple_injective : Function.Injective siteTriple := by
  intro x y h
  have h0 := congrArg (fun p : Lattice3 => p.1) h
  have h1 := congrArg (fun p : Lattice3 => p.2.1) h
  have h2 := congrArg (fun p : Lattice3 => p.2.2) h
  ext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

theorem distance_reverse (x y : Site) :
    latticeDistance (siteTriple y - siteTriple x) = Realization.latticeLength (x - y) := by
  have he (a b : ℤ) : (a - b).natAbs = (b - a).natAbs := by
    rw [← Int.natAbs_neg (a - b), neg_sub]
  simp [latticeDistance, siteTriple, Realization.latticeLength, Fin.sum_univ_succ, add_assoc, he]

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _
attribute [local instance] Classical.propDecidable

def block (i j : SourceDecoration.Vertex S precision) :=
  physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field)
    ((d : ℤ) • P.basis.mulVec (SourceDecoration.site S precision i - SourceDecoration.site S precision j))

def offdiag (i j : SourceDecoration.Vertex S precision) :=
  if i = j then 0 else block P S precision d i j

def far (i j : SourceDecoration.Vertex S precision) :=
  if i = j ∨ SourceDecoration.Incident S precision i j then 0 else block P S precision d i j

theorem block_decay (hd : P.spacing.minimumDistance ≤ d) (i j : SourceDecoration.Vertex S precision)
    (hij : i ≠ j) :
    ‖block P S precision d i j‖ ≤ (P.greenConstant : ℝ) *
      latticeWeight ((P.spacing.r : ℝ)^d)
        (siteTriple (SourceDecoration.site S precision j) - siteTriple (SourceDecoration.site S precision i)) := by
  have hn : SourceDecoration.site S precision i - SourceDecoration.site S precision j ≠ 0 := by
    intro h; exact hij (SourceDecoration.site_injective S precision (sub_eq_zero.mp h))
  calc
    _ ≤ ‖Green.PhysicalCompression.weightedBlock (Maxwell.Defect.ScalarDefect.edgeEmbedding P.defect)
        (Maxwell.Defect.ScalarDefect.coordinateWeight P.defect) (P.bulk.symm : Field →L[ℂ] Field)
        ((d : ℤ) • P.basis.mulVec (SourceDecoration.site S precision i - SourceDecoration.site S precision j))‖ :=
      Maxwell.Defect.realPartOperator_norm_le _
    _ ≤ _ := by
      simpa only [latticeWeight, distance_reverse] using P.green_upper d hd _ hn

theorem offdiag_bound (hd : P.spacing.minimumDistance ≤ d)
    (hhalf : (P.spacing.r : ℝ)^d ≤ 1 / 2) :
    ‖interactionOperator (offdiag P S precision d)‖ ≤ 64 * (P.greenConstant : ℝ) * (P.spacing.r : ℝ)^d := by
  apply lattice_offdiag_operator_norm_le _
    (fun i => siteTriple (SourceDecoration.site S precision i))
    (siteTriple_injective.comp (SourceDecoration.site_injective S precision))
    (P.greenConstant : ℝ) ((P.spacing.r : ℝ)^d)
    (by exact_mod_cast P.greenConstant_nonneg) (by exact_mod_cast (pow_pos P.spacing.r_pos d).le) hhalf
  · intro i; simp [offdiag]
  · intro i j
    by_cases hij : i = j
    · subst j
      simp only [offdiag, ↓reduceIte, norm_zero]
      exact mul_nonneg (by exact_mod_cast P.greenConstant_nonneg)
        (pow_nonneg (pow_pos (by exact_mod_cast P.spacing.r_pos) d).le _)
    · simp only [offdiag, hij, ↓reduceIte]
      exact block_decay P S precision d hd i j hij

theorem far_bound (hd : P.spacing.minimumDistance ≤ d)
    (hhalf : (P.spacing.r : ℝ)^d ≤ 1 / 2) :
    ‖interactionOperator (far P S precision d)‖ ≤
      256 * (P.greenConstant : ℝ) * ((P.spacing.r : ℝ)^d)^2 := by
  apply lattice_interaction_operator_norm_le _
    (fun i => siteTriple (SourceDecoration.site S precision i))
    (siteTriple_injective.comp (SourceDecoration.site_injective S precision))
    (P.greenConstant : ℝ) ((P.spacing.r : ℝ)^d)
    (by exact_mod_cast P.greenConstant_nonneg) (by exact_mod_cast (pow_pos P.spacing.r_pos d).le) hhalf
  · intro i j hnear
    by_cases h : i = j ∨ SourceDecoration.Incident S precision i j
    · simp [far, h]
    · have hf := SourceDecoration.nonincident_distance S precision i j
        (fun he => h (Or.inl he)) (fun he => h (Or.inr he))
      rw [distance_reverse] at hnear
      have hn : (Realization.latticeLength (SourceDecoration.site S precision i - SourceDecoration.site S precision j) : ℤ) < 2 := by
        exact_mod_cast hnear
      simp only [Realization.latticeLength, Nat.cast_sum, Int.natCast_natAbs, Pi.sub_apply] at hn
      simp [Fin.sum_univ_succ] at hn
      omega
  · intro i j
    by_cases h : i = j ∨ SourceDecoration.Incident S precision i j
    · simp only [far, h, ↓reduceIte, norm_zero]
      exact mul_nonneg (by exact_mod_cast P.greenConstant_nonneg)
        (pow_nonneg (pow_pos (by exact_mod_cast P.spacing.r_pos) d).le _)
    · simp only [far, h, ↓reduceIte]
      exact block_decay P S precision d hd i j (fun he => h (Or.inl he))

end PhysicalInteractions
end Maxwell.Composition
