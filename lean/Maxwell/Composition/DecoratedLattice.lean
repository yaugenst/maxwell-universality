import Maxwell.Spectral.Lattice
import Maxwell.Logical.Routing

/-! Doubling the logical cubic lattice and inserting edge midpoints gives
exactly the intended terminal--mediator nearest-neighbor pairs. -/
namespace Maxwell.Composition.DecoratedLattice
open Maxwell.Spectral.Lattice

def Adjacent (x y : Site) : Prop :=
  ∃ k : Direction, y = x + unitSite k ∨ x = y + unitSite k

def terminal (x : Site) : Site := (2 : ℤ) • x

def midpoint (x : Site) (k : Direction) : Site := (2 : ℤ) • x + unitSite k

theorem adjacent_symm {x y : Site} : Adjacent x y ↔ Adjacent y x := by
  simp only [Adjacent, or_comm]

theorem adjacent_iff (x y : Site) : Adjacent x y ↔
    |x 0 - y 0| + |x 1 - y 1| + |x 2 - y 2| = 1 := by
  constructor
  · rintro ⟨k, h | h⟩ <;> subst_vars <;> fin_cases k <;>
      norm_num [unitSite, Pi.single_apply]
  · intro h
    have h0 := abs_nonneg (x 0 - y 0)
    have h1 := abs_nonneg (x 1 - y 1)
    have h2 := abs_nonneg (x 2 - y 2)
    have hcases :
        (y 0 = x 0 + 1 ∧ y 1 = x 1 ∧ y 2 = x 2) ∨
        (x 0 = y 0 + 1 ∧ y 1 = x 1 ∧ y 2 = x 2) ∨
        (y 1 = x 1 + 1 ∧ y 0 = x 0 ∧ y 2 = x 2) ∨
        (x 1 = y 1 + 1 ∧ y 0 = x 0 ∧ y 2 = x 2) ∨
        (y 2 = x 2 + 1 ∧ y 0 = x 0 ∧ y 1 = x 1) ∨
        (x 2 = y 2 + 1 ∧ y 0 = x 0 ∧ y 1 = x 1) := by
      rcases le_total 0 (x 0 - y 0) with ha | ha <;>
        rcases le_total 0 (x 1 - y 1) with hb | hb <;>
        rcases le_total 0 (x 2 - y 2) with hc | hc <;>
        simp only [abs_of_nonneg, abs_of_nonpos, ha, hb, hc] at h0 h1 h2 h <;> omega
    rcases hcases with h | h | h | h | h | h
    · refine ⟨0, Or.inl ?_⟩; ext k; fin_cases k <;> simp [unitSite] <;> omega
    · refine ⟨0, Or.inr ?_⟩; ext k; fin_cases k <;> simp [unitSite] <;> omega
    · refine ⟨1, Or.inl ?_⟩; ext k; fin_cases k <;> simp [unitSite] <;> omega
    · refine ⟨1, Or.inr ?_⟩; ext k; fin_cases k <;> simp [unitSite] <;> omega
    · refine ⟨2, Or.inl ?_⟩; ext k; fin_cases k <;> simp [unitSite] <;> omega
    · refine ⟨2, Or.inr ?_⟩; ext k; fin_cases k <;> simp [unitSite] <;> omega

theorem terminal_injective : Function.Injective terminal := by
  intro x y h
  ext k
  have hk := congrFun h k
  change 2 * x k = 2 * y k at hk
  omega

theorem terminal_ne_midpoint (x y : Site) (k : Direction) : terminal x ≠ midpoint y k := by
  intro h
  have hk := congrFun h k
  simp [terminal, midpoint, unitSite] at hk
  omega

theorem midpoint_injective {x y : Site} {k l : Direction}
    (h : midpoint x k = midpoint y l) : x = y ∧ k = l := by
  have hkl : k = l := by
    by_contra hkl
    have hk := congrFun h k
    simp [midpoint, unitSite, hkl] at hk
    omega
  subst l
  refine ⟨?_, rfl⟩
  ext j
  have hj := congrFun h j
  simp only [midpoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
  omega

theorem terminals_not_adjacent (x y : Site) : ¬ Adjacent (terminal x) (terminal y) := by
  rintro ⟨k, h | h⟩ <;> have hk := congrFun h k <;>
    simp [terminal, unitSite] at hk <;> omega

theorem midpoint_terminal_adjacent (x y : Site) (k : Direction) :
    Adjacent (terminal x) (midpoint y k) ↔ x = y ∨ x = y + unitSite k := by
  constructor
  · rintro ⟨l, h | h⟩
    · have hkl : k = l := by
        by_contra hkl
        have hk := congrFun h k
        simp [terminal, midpoint, unitSite, hkl] at hk
        omega
      subst l
      left
      apply terminal_injective
      exact add_right_cancel h.symm
    · have hkl : k = l := by
        by_contra hkl
        have hk := congrFun h k
        simp [terminal, midpoint, unitSite, hkl] at hk
        omega
      subst l
      right
      ext j
      have hj := congrFun h j
      simp only [terminal, midpoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
      omega
  · rintro (rfl | rfl)
    · exact ⟨k, Or.inl rfl⟩
    · refine ⟨k, Or.inr ?_⟩
      ext j
      simp only [terminal, midpoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

theorem midpoints_not_adjacent (x y : Site) (k l : Direction) :
    ¬ Adjacent (midpoint x k) (midpoint y l) := by
  rintro ⟨j, h | h⟩ <;>
    have h0 := congrFun h 0 <;> have h1 := congrFun h 1 <;> have h2 := congrFun h 2 <;>
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [midpoint, unitSite, Pi.single_apply] at h0 h1 h2 <;> omega

end Maxwell.Composition.DecoratedLattice
