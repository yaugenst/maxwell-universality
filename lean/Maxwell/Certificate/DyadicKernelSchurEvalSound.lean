import Maxwell.Certificate.DyadicKernelSchurEval
import Maxwell.Certificate.DyadicKernelRoundedDivision

namespace Maxwell.Certificate.DyadicKernel
open scoped ComplexOrder

@[simp] theorem Rows.enclosure_ofEnclosure {n : ℕ} (a : Enclosure n) :
    (Rows.ofEnclosure a).enclosure = a := by
  ext i j
  simp [Rows.ofEnclosure, Rows.enclosure]

@[simp] theorem schurUpdateRows_entry (p : ℕ) {n : ℕ} (a : Rows (n+1)) (i j : Fin n) :
    (schurUpdateRows p a).enclosure i j = schurUpdateEntry p
      (a.enclosure i.succ j.succ) (a.enclosure i.succ 0) (a.enclosure j.succ 0)
      (a.enclosure 0 0) := by
  simp [schurUpdateRows, Rows.enclosure]

theorem divRound_getD_of_pos (p : ℕ) (a b : Rectangle)
    (hp : 0 < b.re-(b.radius : ℤ)) :
    divRound p a b = some ((divRound p a b).getD zero) := by
  cases a
  cases b
  simp_all [divRound]

theorem schurUpdateEntry_contains {p : ℕ} {aij ai0 aj0 pivot : Rectangle}
    {z u v : ℂ} {d : ℝ} (hp : 0 < pivot.re-(pivot.radius : ℤ))
    (hz : aij.toDyadic.Contains p z) (hu : ai0.toDyadic.Contains p u)
    (hv : aj0.toDyadic.Contains p v) (hd : pivot.toDyadic.Contains p (d : ℂ)) :
    (schurUpdateEntry p aij ai0 aj0 pivot).toDyadic.Contains p
      (z-u*star v/(d : ℂ)) := by
  have hv' : (conjugate aj0).toDyadic.Contains p (star v) := by
    rw [toDyadic_conjugate]
    exact DyadicRectangle.conjugate_contains hv
  have hm := mulRound_contains hu hv'
  have hq := divRound_contains (divRound_getD_of_pos p _ pivot hp) hm hd
  unfold schurUpdateEntry
  rw [toDyadic_add, toDyadic_neg]
  exact DyadicRectangle.add_contains hz (DyadicRectangle.neg_contains hq)

theorem schurUpdateRows_contains {p n : ℕ} {a : Rows (n+1)}
    {A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ}
    (hA : A.IsHermitian) (hp : 0 < (a.enclosure 0 0).re-((a.enclosure 0 0).radius : ℤ))
    (ha : MatrixContains p a.enclosure A) :
    MatrixContains p (schurUpdateRows p a).enclosure (SchurStep.schur A) := by
  intro i j
  rw [schurUpdateRows_entry]
  exact schurUpdateEntry_contains hp (ha i.succ j.succ) (ha i.succ 0) (ha j.succ 0)
    ((SchurStep.diagonal_eq_real hA) ▸ ha 0 0)

theorem schurEvalRows_posDef {p n : ℕ} {a : Rows n}
    (h : schurEvalRows p a = true) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (ha : MatrixContains p a.enclosure A) : A.PosDef := by
  induction n with
  | zero =>
      apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
      intro x hx
      exact (hx (funext fun i => Fin.elim0 i)).elim
  | succ n ih =>
      simp only [schurEvalRows, Bool.and_eq_true_iff] at h
      have hp := of_decide_eq_true h.1
      apply SchurStep.posDef_of_schur hA (positive_pivot hp ha)
      exact ih h.2 (SchurStep.schur_isHermitian hA) (schurUpdateRows_contains hA hp ha)

/-- Kernel acceptance of the deterministic evaluator proves strict positive
definiteness of every Hermitian matrix enclosed by the input rectangles. -/
theorem schurEval_posDef {p n : ℕ} {a : Enclosure n}
    (h : schurEval p a = true) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (ha : MatrixContains p a A) : A.PosDef := by
  apply schurEvalRows_posDef h hA
  simpa only [Rows.enclosure_ofEnclosure] using ha

end Maxwell.Certificate.DyadicKernel
