import Maxwell.Continuum.MonotoneCrossing

/-! Finite singular-parameter counting on the actual parameter window.
No positivity or even physical definition is required outside the window. -/

noncomputable section

namespace Maxwell.Continuum.WindowCrossing

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (W : Set ℝ) (A : W → H →ₗ[ℂ] H) (hA : ∀ t, (A t).IsSymmetric)
variable (hmono : ∀ a b : W, (a : ℝ) ≤ b → ∀ x : H,
  (inner ℂ x (A b x)).re ≤ (inner ℂ x (A a x)).re - ((b : ℝ) - a) * ‖x‖ ^ 2)

def extension (t : ℝ) : H →ₗ[ℂ] H := by
  classical
  exact if h : t ∈ W then A ⟨t, h⟩ else 0

@[simp] theorem extension_apply (t : W) : extension W A t = A t := by
  classical
  exact dite_eq_left t.property

include hA in
theorem extension_symmetric (t : ℝ) : (extension W A t).IsSymmetric := by
  classical
  unfold extension
  split
  · exact hA _
  · intro x y
    simp

include hmono in
theorem extension_decrease (a : ℝ) (ha : a ∈ W) (b : ℝ) (hb : b ∈ W)
    (hab : a ≤ b) (x : H) :
    (inner ℂ x (extension W A b x)).re ≤ (inner ℂ x (extension W A a x)).re -
      (b - a) * ‖x‖ ^ 2 := by
  have ea := extension_apply W A (⟨a, ha⟩ : W)
  have eb := extension_apply W A (⟨b, hb⟩ : W)
  change extension W A a = A ⟨a, ha⟩ at ea
  change extension W A b = A ⟨b, hb⟩ at eb
  rw [ea, eb]
  exact hmono ⟨a, ha⟩ ⟨b, hb⟩ hab x

variable [FiniteDimensional ℂ H]

def singularParameters : Finset ℝ :=
  MonotoneCrossing.zeroFinset (extension W A) (extension_symmetric W A hA) W
    (extension_decrease W A hmono)

theorem singularParameters_card_le :
    (singularParameters W A hA hmono).card ≤ Module.finrank ℂ H :=
  MonotoneCrossing.zeroFinset_card_le _ _ _ _

theorem mem_singularParameters (t : W) :
    (t : ℝ) ∈ singularParameters W A hA hmono ↔ (A t).ker ≠ ⊥ := by
  rw [singularParameters, MonotoneCrossing.mem_zeroFinset_iff_kernel]
  rw [extension_apply W A t]
  exact and_iff_right t.property

theorem singularParameters_subset : ↑(singularParameters W A hA hmono) ⊆ W := by
  intro t ht
  exact (MonotoneCrossing.mem_zeroFinset _ _ _ _ t).mp ht |>.1

end Maxwell.Continuum.WindowCrossing
