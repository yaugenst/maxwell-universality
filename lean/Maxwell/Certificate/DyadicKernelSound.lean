import Maxwell.Certificate.DyadicKernel
import Maxwell.Certificate.DyadicList
import Maxwell.Certificate.DyadicScale

namespace Maxwell.Certificate.DyadicKernel

def Rectangle.toDyadic : Rectangle → DyadicRectangle
  | ⟨r,i,e⟩ => ⟨r,i,e⟩

theorem toDyadic_add (a b : Rectangle) :
    (add a b).toDyadic = a.toDyadic.add b.toDyadic := by cases a; cases b; rfl

theorem toDyadic_conjugate (a : Rectangle) :
    (conjugate a).toDyadic = a.toDyadic.conjugate := by cases a; rfl

theorem toDyadic_mulExact (a b : Rectangle) :
    (mulExact a b).toDyadic = DyadicRectangle.mulExact a.toDyadic b.toDyadic := by
  cases a with | mk ar ai ae =>
    cases b with | mk br bi be =>
      simp only [mulExact, Rectangle.toDyadic, DyadicRectangle.mulExact, DyadicRectangle.mulError]
      congr 1
      have h : (((ar.natAbs+ai.natAbs)*be+(br.natAbs+bi.natAbs)*ae+2*ae*be:ℕ):ℤ) =
          (|ar|+|ai|)*be+(|br|+|bi|)*ae+2*(ae:ℤ)*be := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_natAbs]
      simpa only [Int.toNat_natCast] using congrArg Int.toNat h

theorem toDyadic_dot (a : List (Rectangle × Rectangle)) :
    (dot a).toDyadic = DyadicRectangle.dotPairs
      (a.map (fun p => (p.1.toDyadic,p.2.toDyadic))) := by
  induction a with
  | nil => rfl
  | cons pair tail ih =>
    rcases pair with ⟨a,b⟩
    simp only [dot, toDyadic_add, toDyadic_mulExact, List.map_cons,
      DyadicRectangle.dotPairs, DyadicRectangle.mulExactFast_eq, ih]

theorem rescaleCheck_eq (p q : ℕ) (a b : Rectangle) :
    rescaleCheck q a b = DyadicRectangle.rescaleCheck p q a.toDyadic b.toDyadic := by
  cases a with | mk ar ai ae =>
    cases b with | mk br bi be =>
      simp only [rescaleCheck, Rectangle.toDyadic, DyadicRectangle.rescaleCheck]
      congr 1
      apply propext
      simp only [← Int.natCast_natAbs]
      constructor <;> intro h <;> constructor
      all_goals
        first
        | exact_mod_cast h.1
        | exact_mod_cast h.2

theorem dotCheck_eq (p q : ℕ) (a : List (Rectangle × Rectangle)) (b : Rectangle) :
    dotCheck q a b = DyadicRectangle.listDotCheck p q
      (a.map (fun pair => (pair.1.toDyadic,pair.2.toDyadic))) b.toDyadic := by
  rw [dotCheck, rescaleCheck_eq p q, toDyadic_dot]
  rfl

theorem scaleCheck_eq (num den : ℤ) (a b : Rectangle) :
    scaleCheck num den a b = DyadicRectangle.scaleCheck num den a.toDyadic b.toDyadic := by
  cases a; cases b
  simp only [scaleCheck, Rectangle.toDyadic, DyadicRectangle.scaleCheck, Int.ofNat_eq_natCast, Int.natCast_natAbs]
  congr 1

theorem subsetCheck_eq (a b : Rectangle) :
    subsetCheck a b = DyadicRectangle.subsetCheck a.toDyadic b.toDyadic := by
  cases a with | mk ar ai ae =>
    cases b with | mk br bi be =>
      simp only [subsetCheck, Rectangle.toDyadic, DyadicRectangle.subsetCheck]
      congr 1
      apply propext
      simp only [← Int.natCast_natAbs]
      constructor <;> intro h <;> constructor
      all_goals
        first
        | exact_mod_cast h.1
        | exact_mod_cast h.2

end Maxwell.Certificate.DyadicKernel
