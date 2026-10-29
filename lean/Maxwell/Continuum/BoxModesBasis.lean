import Maxwell.Continuum.BoxModesOperator
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# A concrete complete orthonormal basis of the physical box field space

The basis consists of normalized zero-extended mixed sine/cosine component
modes. Orthogonality uses the exact continuum integrals and completeness
uses the proved Stone–Weierstrass/L² density theorem.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped InnerProductSpace BigOperators

theorem restrict_zeroExtendedBoxMode (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) :
    restrictBoxL2 N (zeroExtendedBoxMode N c ν) = boxComplexModeL2 N c ν := by
  apply Lp.ext
  filter_upwards [restrictBoxL2_coe_ae N (zeroExtendedBoxMode N c ν),
    ae_restrict_of_ae (zeroExtendedBoxMode_coe_ae N c ν),
    ae_restrict_mem (isOpen_openBox N).measurableSet,
    boxComplexModeL2_coe_ae N c ν] with x hr hz hΩ hb
  rw [hr, hz, Set.indicator_of_mem hΩ, hb]

theorem zeroExtendedBoxMode_inner_mode (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (c : Fin 3) (ν μ : Fin 3 → ℤ)
    (hν : AdmissibleIndex c ν) (hμ : AdmissibleIndex c μ) :
    inner ℂ (zeroExtendedBoxMode N c ν) (zeroExtendedBoxMode N c μ) =
      if ν = μ then (∏ j : Fin 3, coordinateSquareNorm N ν c j : ℝ) else 0 := by
  rw [zeroExtendedBoxMode_inner, restrict_zeroExtendedBoxMode, L2.inner_def]
  calc
    (∫ x in openBox N, inner ℂ (boxComplexModeL2 N c ν x) (boxComplexModeL2 N c μ x)) =
        ∫ x in openBox N, ((scalarBoxMode N ν c x * scalarBoxMode N μ c x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [boxComplexModeL2_coe_ae N c ν, boxComplexModeL2_coe_ae N c μ]
        with x hνx hμx
      rw [hνx, hμx, RCLike.inner_apply']
      simp only [Complex.conj_ofReal, ← Complex.ofReal_mul]
    _ = _ := by
      rw [integral_complex_ofReal, integral_scalarBoxMode_mul N hN ν μ c hν hμ]

theorem componentMode_inner_same (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (c : Fin 3) (ν μ : Fin 3 → ℤ)
    (hν : AdmissibleIndex c ν) (hμ : AdmissibleIndex c μ) :
    inner ℂ (componentMode N c ν) (componentMode N c μ) =
      if ν = μ then (∏ j : Fin 3, coordinateSquareNorm N ν c j : ℝ) else 0 := by
  change inner ℂ (PiLp.single 2 c (zeroExtendedBoxMode N c ν) : FieldL2)
    (PiLp.single 2 c (zeroExtendedBoxMode N c μ) : FieldL2) = _
  rw [field_inner_single_left, PiLp.single_eq_same]
  exact zeroExtendedBoxMode_inner_mode N hN c ν μ hν hμ

theorem componentMode_inner_ne_component (N : Fin 3 → ℝ) (c d : Fin 3)
    (ν μ : Fin 3 → ℤ) (hcd : c ≠ d) :
    inner ℂ (componentMode N c ν) (componentMode N d μ) = 0 := by
  change inner ℂ (PiLp.single 2 c (zeroExtendedBoxMode N c ν) : FieldL2)
    (PiLp.single 2 d (zeroExtendedBoxMode N d μ) : FieldL2) = _
  rw [field_inner_single_left, PiLp.single_eq_of_ne 2 hcd, inner_zero_right]

def indexedComponentMode (N : Fin 3 → ℝ) (q : ComponentModeIndex) :
    testL2Closure (boxDomain N) := componentMode N q.1 q.2.val

theorem indexedComponentMode_ne_zero (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (q : ComponentModeIndex) : indexedComponentMode N q ≠ 0 := by
  intro hz
  have hi := componentMode_inner_same N hN q.1 q.2.val q.2.val q.2.property q.2.property
  change inner ℂ (indexedComponentMode N q) (indexedComponentMode N q) = _ at hi
  rw [hz, inner_zero_left, ite_eq_left rfl] at hi
  have hp := scalarBoxMode_squareNorm_pos N hN q.2.val q.1
  have he : (∏ j : Fin 3, coordinateSquareNorm N q.2.val q.1 j) = 0 := by
    exact_mod_cast hi.symm
  exact (ne_of_gt hp) he

theorem indexedComponentMode_orthogonal (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    {q r : ComponentModeIndex} (hqr : q ≠ r) :
    inner ℂ (indexedComponentMode N q) (indexedComponentMode N r) = 0 := by
  rcases q with ⟨c, ν, hν⟩
  rcases r with ⟨d, μ, hμ⟩
  change inner ℂ (componentMode N c ν) (componentMode N d μ) = 0
  by_cases hcd : c = d
  · subst d
    rw [componentMode_inner_same N hN c ν μ hν hμ]
    have hνμ : ν ≠ μ := by
      intro h
      subst μ
      exact hqr rfl
    simp [hνμ]
  · exact componentMode_inner_ne_component N c d ν μ hcd

def normalizedComponentMode (N : Fin 3 → ℝ) (q : ComponentModeIndex) :
    testL2Closure (boxDomain N) :=
  (‖indexedComponentMode N q‖⁻¹ : ℂ) • indexedComponentMode N q

theorem normalizedComponentMode_orthonormal (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) :
    Orthonormal ℂ (normalizedComponentMode N) := by
  constructor
  · intro q
    exact norm_smul_inv_norm (indexedComponentMode_ne_zero N hN q)
  · intro q r hqr
    rw [normalizedComponentMode, normalizedComponentMode, inner_smul_left, inner_smul_right,
      indexedComponentMode_orthogonal N hN hqr, mul_zero, mul_zero]

theorem indexedComponentMode_eq_norm_smul (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (q : ComponentModeIndex) :
    indexedComponentMode N q = (‖indexedComponentMode N q‖ : ℂ) • normalizedComponentMode N q := by
  rw [normalizedComponentMode, smul_smul,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (indexedComponentMode_ne_zero N hN q))), one_smul]

theorem normalizedComponentMode_orthogonal_eq_bot (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) :
    (Submodule.span ℂ (Set.range (normalizedComponentMode N)))ᗮ = ⊥ := by
  apply le_antisymm
  · intro u hu
    have hraw : (u : FieldL2) ∈ (componentBoxModeSpan N)ᗮ := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨q, rfl⟩ := hv
        change inner ℂ (indexedComponentMode N q) u = 0
        rw [indexedComponentMode_eq_norm_smul N hN q, inner_smul_left,
          hu _ (Submodule.subset_span ⟨q, rfl⟩), mul_zero]
      | zero => exact inner_zero_left _
      | add v w _ _ hv hw => rw [inner_add_left, hv, hw, add_zero]
      | smul a v _ hv => rw [inner_smul_left, hv, mul_zero]
    have hself : inner ℂ u u = 0 := by
      rw [← Submodule.orthogonal_closure, componentBoxMode_complete N hN] at hraw
      exact hraw _ u.property
    exact (inner_self_eq_zero.mp hself : u = 0)
  · exact bot_le

/-- The complete Fourier Hilbert basis of the actual supported complex L²
field space. No Fourier completeness or operator-domain axiom is used. -/
def componentHilbertBasis (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) :
    HilbertBasis ComponentModeIndex ℂ (testL2Closure (boxDomain N)) :=
  HilbertBasis.mkOfOrthogonalEqBot (normalizedComponentMode_orthonormal N hN)
    (normalizedComponentMode_orthogonal_eq_bot N hN)

@[simp] theorem componentHilbertBasis_apply (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (q : ComponentModeIndex) : componentHilbertBasis N hN q = normalizedComponentMode N q :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) q

#print axioms componentHilbertBasis

end Maxwell.Continuum.BoxModes
