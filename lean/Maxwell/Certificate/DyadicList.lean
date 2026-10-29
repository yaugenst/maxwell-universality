import Maxwell.Certificate.DyadicRectangle
import Mathlib.Data.List.OfFn

/-! Structurally matched integer dot products. These definitions have the
same checked semantics as `dotCheck`, with fewer repeated record projections. -/
namespace Maxwell.Certificate.DyadicRectangle

def mulExactFast : DyadicRectangle → DyadicRectangle → DyadicRectangle
  | ⟨ar, ai, ae⟩, ⟨br, bi, be⟩ =>
      ⟨ar*br-ai*bi, ar*bi+ai*br,
       ((|ar|+|ai|)*(be:ℤ)+(|br|+|bi|)*(ae:ℤ)+2*(ae:ℤ)*be).toNat⟩

theorem mulExactFast_eq (a b : DyadicRectangle) : mulExactFast a b = mulExact a b := by
  cases a
  cases b
  rfl

def sumProductsFast : {n : ℕ} → (Fin n → DyadicRectangle) →
    (Fin n → DyadicRectangle) → DyadicRectangle
  | 0, _, _ => zero
  | _+1, a, b => (mulExactFast (a 0) (b 0)).add
      (sumProductsFast (fun i => a i.succ) (fun i => b i.succ))

theorem sumProductsFast_eq {n : ℕ} (a b : Fin n → DyadicRectangle) :
    sumProductsFast a b = sum fun i => mulExact (a i) (b i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumProductsFast, sum, mulExactFast_eq, ih]

def fastDotCheck {n : ℕ} (p q : ℕ) (a b : Fin n → DyadicRectangle)
    (c : DyadicRectangle) : Bool := rescaleCheck p q (sumProductsFast a b) c

theorem fastDotCheck_eq {n : ℕ} (p q : ℕ) (a b : Fin n → DyadicRectangle)
    (c : DyadicRectangle) : fastDotCheck p q a b c = dotCheck p q a b c := by
  simp only [fastDotCheck, dotCheck, sumProductsFast_eq]

theorem fastDotCheck_sound {n p q : ℕ} {a b : Fin n → DyadicRectangle}
    {c : DyadicRectangle} {z w : Fin n → ℂ}
    (h : fastDotCheck p q a b c = true)
    (ha : ∀ i, (a i).Contains p (z i)) (hb : ∀ i, (b i).Contains q (w i)) :
    c.Contains p (∑ i, z i*w i) :=
  dotCheck_sound ((fastDotCheck_eq p q a b c).symm.trans h) ha hb

def dotPairs : List (DyadicRectangle × DyadicRectangle) → DyadicRectangle
  | [] => zero
  | (a,b)::tail => (mulExactFast a b).add (dotPairs tail)

theorem dotPairs_contains {p q : ℕ}
    {data : List (DyadicRectangle × DyadicRectangle)} {values : List (ℂ × ℂ)}
    (h : List.Forall₂ (fun ab zw => ab.1.Contains p zw.1 ∧ ab.2.Contains q zw.2) data values) :
    (dotPairs data).Contains (p+q) (values.map (fun zw => zw.1*zw.2)).sum := by
  induction h with
  | nil => exact zero_contains _
  | cons hh ht ih =>
      simpa only [dotPairs, mulExactFast_eq, List.map_cons, List.sum_cons] using
        add_contains (mulExact_contains hh.1 hh.2) ih

theorem dotPairs_ofFn_eq {n : ℕ} (a b : Fin n → DyadicRectangle) :
    dotPairs (List.ofFn fun i => (a i,b i)) = sumProductsFast a b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.ofFn_succ, dotPairs, sumProductsFast, ih]

def listDotCheck (p q : ℕ) (data : List (DyadicRectangle × DyadicRectangle))
    (c : DyadicRectangle) : Bool := rescaleCheck p q (dotPairs data) c

theorem listDotCheck_sound {p q : ℕ}
    {data : List (DyadicRectangle × DyadicRectangle)} {values : List (ℂ × ℂ)}
    {c : DyadicRectangle} (h : listDotCheck p q data c = true)
    (hd : List.Forall₂ (fun ab zw => ab.1.Contains p zw.1 ∧ ab.2.Contains q zw.2) data values) :
    c.Contains p (values.map (fun zw => zw.1*zw.2)).sum :=
  rescaleCheck_sound h (dotPairs_contains hd)

theorem listDotCheck_ofFn_eq {n : ℕ} (p q : ℕ) (a b : Fin n → DyadicRectangle)
    (c : DyadicRectangle) :
    listDotCheck p q (List.ofFn fun i => (a i,b i)) c = dotCheck p q a b c := by
  simp only [listDotCheck, dotPairs_ofFn_eq, dotCheck, sumProductsFast_eq]

theorem dotCheck_of_list {n p q : ℕ} {a b : Fin n → DyadicRectangle}
    {data : List (DyadicRectangle × DyadicRectangle)} {c : DyadicRectangle}
    (he : data = List.ofFn fun i => (a i,b i)) (h : listDotCheck p q data c = true) :
    dotCheck p q a b c = true := by
  rw [he, listDotCheck_ofFn_eq] at h
  exact h

end Maxwell.Certificate.DyadicRectangle
