import Maxwell.Certificate.DyadicList

namespace Maxwell.Certificate.DyadicRectangle

theorem zip_ofFn {α β : Type*} {n : ℕ} (a : Fin n → α) (b : Fin n → β) :
    (List.ofFn a).zip (List.ofFn b) = List.ofFn (fun i => (a i, b i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.ofFn_succ, List.zip_cons_cons, ih]

theorem dotCheck_of_zip {n p q : ℕ} {a b : Fin n → DyadicRectangle}
    {as bs : List DyadicRectangle} {c : DyadicRectangle}
    (ha : as = List.ofFn a) (hb : bs = List.ofFn b)
    (h : listDotCheck p q (as.zip bs) c = true) : dotCheck p q a b c = true := by
  apply dotCheck_of_list _ h
  rw [ha, hb, zip_ofFn]

end Maxwell.Certificate.DyadicRectangle
