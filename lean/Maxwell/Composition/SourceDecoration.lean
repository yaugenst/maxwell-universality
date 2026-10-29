import Maxwell.Composition.SourceIncidence

/-! Actual physical defect sites: twice each routed vertex and one midpoint
of every routed edge. Parity eliminates all unintended nearest neighbors. -/
noncomputable section
namespace Maxwell.Composition.SourceDecoration
open Maxwell.Spectral.Lattice
open Maxwell.Composition.DecoratedLattice
open Maxwell.Composition.TranslatedStencil

variable (S : Source.SparseSystem) (precision : ℕ)

abbrev Vertex := SourceIncidence.V S precision ⊕ SourceIncidence.E S precision

def site : Vertex S precision → Site
  | .inl v => terminal (SourceIncidence.position S precision v)
  | .inr e => SourceIncidence.position S precision e.val.1 + SourceIncidence.position S precision e.val.2

theorem mediator_site (e : SourceIncidence.E S precision) :
    site S precision (.inr e) = DecoratedLattice.midpoint (SourceIncidence.position S precision e.val.1)
      (SourceIncidence.axis S precision e) := by
  rw [site, SourceIncidence.axis_spec]
  ext k
  simp only [DecoratedLattice.midpoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem site_injective : Function.Injective (site S precision) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact congrArg Sum.inl (SourceDefectLayout.position_injective S precision (terminal_injective h))
    | inr b =>
      rw [mediator_site] at h
      exact (terminal_ne_midpoint _ _ _ h).elim
  | inr a =>
    cases b with
    | inl b =>
      rw [mediator_site] at h
      exact (terminal_ne_midpoint _ _ _ h.symm).elim
    | inr b =>
      rw [mediator_site, mediator_site] at h
      obtain ⟨hp, ha⟩ := midpoint_injective h
      have ht := SourceDefectLayout.position_injective S precision hp
      have hh : a.val.2 = b.val.2 := by
        apply SourceDefectLayout.position_injective S precision
        change SourceIncidence.position S precision a.val.2 = SourceIncidence.position S precision b.val.2
        exact (SourceIncidence.axis_spec S precision a).trans
          ((congrArg₂ (fun x k => x + unitSite k) hp ha).trans (SourceIncidence.axis_spec S precision b).symm)
      apply congrArg Sum.inr
      exact Subtype.ext (Prod.ext ht hh)

def Incident : Vertex S precision → Vertex S precision → Prop
  | .inl v, .inr e => v = e.val.1 ∨ v = e.val.2
  | .inr e, .inl v => v = e.val.1 ∨ v = e.val.2
  | _, _ => False

theorem adjacent_iff_incident (a b : Vertex S precision) :
    Adjacent (site S precision a) (site S precision b) ↔ Incident S precision a b := by
  have hm (v : SourceIncidence.V S precision) (e : SourceIncidence.E S precision) :
      Adjacent (site S precision (.inl v)) (site S precision (.inr e)) ↔
        v = e.val.1 ∨ v = e.val.2 := by
    rw [mediator_site]
    change Adjacent (terminal _) (DecoratedLattice.midpoint _ _) ↔ _
    rw [midpoint_terminal_adjacent, ← SourceIncidence.axis_spec]
    exact or_congr (SourceDefectLayout.position_injective S precision).eq_iff
      (SourceDefectLayout.position_injective S precision).eq_iff
  cases a with
  | inl a =>
    cases b with
    | inl b => exact iff_false_intro (terminals_not_adjacent _ _)
    | inr b => exact hm a b
  | inr a =>
    cases b with
    | inl b => exact adjacent_symm.trans (hm b a)
    | inr b =>
      rw [mediator_site, mediator_site]
      exact iff_false_intro (midpoints_not_adjacent _ _ _ _)

/-- Every other pair is at integer lattice distance at least two; this
is the separation used in the complete off-incidence Green estimate. -/
theorem nonincident_distance (a b : Vertex S precision) (hab : a ≠ b)
    (hnot : ¬ Incident S precision a b) :
    2 ≤ |site S precision a 0 - site S precision b 0| +
      |site S precision a 1 - site S precision b 1| +
      |site S precision a 2 - site S precision b 2| := by
  have h0 := abs_nonneg (site S precision a 0 - site S precision b 0)
  have h1 := abs_nonneg (site S precision a 1 - site S precision b 1)
  have h2 := abs_nonneg (site S precision a 2 - site S precision b 2)
  have hn1 : |site S precision a 0 - site S precision b 0| +
      |site S precision a 1 - site S precision b 1| +
      |site S precision a 2 - site S precision b 2| ≠ 1 := by
    intro h
    exact hnot ((adjacent_iff_incident S precision a b).mp ((adjacent_iff _ _).mpr h))
  have hn0 : |site S precision a 0 - site S precision b 0| +
      |site S precision a 1 - site S precision b 1| +
      |site S precision a 2 - site S precision b 2| ≠ 0 := by
    intro h
    apply hab
    apply site_injective S precision
    have hz0 := abs_eq_zero.mp (show |site S precision a 0 - site S precision b 0| = 0 by omega)
    have hz1 := abs_eq_zero.mp (show |site S precision a 1 - site S precision b 1| = 0 by omega)
    have hz2 := abs_eq_zero.mp (show |site S precision a 2 - site S precision b 2| = 0 by omega)
    ext k
    fin_cases k
    · exact sub_eq_zero.mp hz0
    · exact sub_eq_zero.mp hz1
    · exact sub_eq_zero.mp hz2
  omega

def baseBox : Target.Box where
  nx := 2 * (SourceDefectLayout.baseBox S precision).nx
  ny := 2 * (SourceDefectLayout.baseBox S precision).ny
  nz := 2 * (SourceDefectLayout.baseBox S precision).nz

theorem site_inside (v : Vertex S precision) (k : Direction) :
    0 ≤ site S precision v k ∧ site S precision v k < (Green.boxSide (baseBox S precision) k : ℤ) := by
  have hs : Green.boxSide (baseBox S precision) k =
      2 * Green.boxSide (SourceDefectLayout.baseBox S precision) k := by fin_cases k <;> rfl
  rw [hs]
  cases v with
  | inl v =>
    have h := latticeCell_bounds (SourceDefectLayout.baseBox S precision)
      (SourceDefectLayout.indices S precision v) k
    change 0 ≤ 2 * SourceIncidence.position S precision v k ∧
      2 * SourceIncidence.position S precision v k < _
    change 0 ≤ SourceIncidence.position S precision v k ∧
      SourceIncidence.position S precision v k < (Green.boxSide (SourceDefectLayout.baseBox S precision) k : ℤ) at h
    push_cast
    omega
  | inr e =>
    have h₁ := latticeCell_bounds (SourceDefectLayout.baseBox S precision)
      (SourceDefectLayout.indices S precision e.val.1) k
    have h₂ := latticeCell_bounds (SourceDefectLayout.baseBox S precision)
      (SourceDefectLayout.indices S precision e.val.2) k
    change 0 ≤ SourceIncidence.position S precision e.val.1 k ∧
      SourceIncidence.position S precision e.val.1 k < (Green.boxSide (SourceDefectLayout.baseBox S precision) k : ℤ) at h₁
    change 0 ≤ SourceIncidence.position S precision e.val.2 k ∧
      SourceIncidence.position S precision e.val.2 k < (Green.boxSide (SourceDefectLayout.baseBox S precision) k : ℤ) at h₂
    change 0 ≤ SourceIncidence.position S precision e.val.1 k + SourceIncidence.position S precision e.val.2 k ∧ _
    dsimp only [site, Pi.add_apply]
    push_cast
    omega

def indices (v : Vertex S precision) : (baseBox S precision).Cell :=
  finiteCell _ _ (site_inside S precision v)

@[simp] theorem indices_lattice (v : Vertex S precision) :
    Target.latticeCell (indices S precision v) = site S precision v := lattice_finiteCell _ _ _

theorem indices_injective : Function.Injective (indices S precision) := by
  intro a b h
  apply site_injective S precision
  simpa only [indices_lattice] using congrArg Target.latticeCell h

end Maxwell.Composition.SourceDecoration
