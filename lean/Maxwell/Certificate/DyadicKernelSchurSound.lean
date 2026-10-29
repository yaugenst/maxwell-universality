import Maxwell.Certificate.DyadicKernelSchur
import Maxwell.Certificate.DyadicKernelMagneticSound
import Maxwell.Certificate.DyadicDivision
import Maxwell.Certificate.IntervalMatrixPosDef

namespace Maxwell.Certificate.DyadicKernel
open scoped ComplexOrder

theorem divCheck_eq (p : ℕ) (a b c : Rectangle) :
    divCheck p a b c = DyadicRectangle.divCheck p a.toDyadic b.toDyadic c.toDyadic := by
  cases a; cases b; cases c; rfl

theorem toDyadic_neg (a : Rectangle) :
    (neg a).toDyadic = a.toDyadic.neg := by cases a; rfl

def MatrixContains {n : ℕ} (p : ℕ) (a : Enclosure n)
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j, (a i j).toDyadic.Contains p (A i j)

theorem positive_pivot {p n : ℕ} {a : Enclosure (n+1)}
    {A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ}
    (hp : 0 < (a 0 0).re - ((a 0 0).radius : ℤ)) (ha : MatrixContains p a A) :
    0 < (A 0 0).re := by
  have hp' : (0 : ℝ) < ((a 0 0).re : ℝ) - (a 0 0).radius := by exact_mod_cast hp
  have hh := (abs_le.mp (ha 0 0).1).1
  have hs : (0 : ℝ) < 2^p := by positivity
  change -((a 0 0).radius : ℝ) ≤ (A 0 0).re * 2^p - ((a 0 0).re : ℝ) at hh
  nlinarith

theorem schurEntryCheck_contains {p : ℕ}
    {aij ai0 aj0 pivot product quotient result : Rectangle}
    {z u v : ℂ} {d : ℝ}
    (h : schurEntryCheck p aij ai0 aj0 pivot product quotient result = true)
    (hz : aij.toDyadic.Contains p z) (hu : ai0.toDyadic.Contains p u)
    (hv : aj0.toDyadic.Contains p v) (hd : pivot.toDyadic.Contains p (d : ℂ)) :
    result.toDyadic.Contains p (z - u * star v / (d : ℂ)) := by
  simp only [schurEntryCheck, Bool.and_eq_true_iff] at h
  have hm := h.1.1
  rw [rescaleCheck_eq p p, toDyadic_mulExact, toDyadic_conjugate] at hm
  have hp := DyadicRectangle.rescaleCheck_sound hm
    (DyadicRectangle.mulExact_contains hu (DyadicRectangle.conjugate_contains hv))
  have hq := h.1.2
  rw [divCheck_eq] at hq
  have hquot := DyadicRectangle.divCheck_sound hq hp hd
  have hr := h.2
  rw [subsetCheck_eq, toDyadic_add, toDyadic_neg] at hr
  exact DyadicRectangle.subsetCheck_sound hr
    (DyadicRectangle.add_contains hz (DyadicRectangle.neg_contains hquot))

theorem schurAccepts_posDef {p n : ℕ} {a : Enclosure n} (w : SchurProposal n)
    (h : schurAccepts p a w = true) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (ha : MatrixContains p a A) : A.PosDef := by
  induction w with
  | empty =>
      apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
      intro x hx
      exact (hx (funext fun i => Fin.elim0 i)).elim
  | @next n b products quotients tail ih =>
      simp only [schurAccepts, Bool.and_eq_true_iff] at h
      have hp := of_decide_eq_true h.1.1
      have he := of_decide_eq_true h.1.2
      apply SchurStep.posDef_of_schur hA (positive_pivot hp ha)
      apply ih h.2 (SchurStep.schur_isHermitian hA)
      intro i j
      exact schurEntryCheck_contains (he i j) (ha i.succ j.succ)
        (ha i.succ 0) (ha j.succ 0)
        ((SchurStep.diagonal_eq_real hA) ▸ ha 0 0)

end Maxwell.Certificate.DyadicKernel
