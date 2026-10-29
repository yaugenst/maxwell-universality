import Maxwell.Certificate.DyadicKernelSound
import Maxwell.Certificate.DyadicListRows

namespace Maxwell.Certificate.DyadicKernel

theorem dotCheck_of_lists {n p q : ℕ} (a b : Fin n → Rectangle) (c : Rectangle)
    (as bs : List Rectangle) (ha : as = List.ofFn a) (hb : bs = List.ofFn b)
    (h : dotCheck q (as.zip bs) c = true) :
    DyadicRectangle.dotCheck p q (fun i => (a i).toDyadic)
      (fun i => (b i).toDyadic) c.toDyadic = true := by
  rw [dotCheck_eq p q, ha, hb, DyadicRectangle.zip_ofFn, List.map_ofFn,
    DyadicRectangle.listDotCheck_ofFn_eq] at h
  exact h

/-- A line of all output dot products. Exact list identities bind every
coordinate and length to the finite input, coefficient, and output maps. -/
theorem line_of_lists {n m p q : ℕ}
    (a : Fin n → Rectangle) (K : Fin m → Fin n → Rectangle) (b : Fin m → Rectangle)
    (input : List Rectangle) (coefficients : List (List Rectangle)) (output : List Rectangle)
    (hi : input = List.ofFn a)
    (hK : coefficients = List.ofFn (fun i => List.ofFn (K i)))
    (ho : output = List.ofFn b)
    (h : (coefficients.zip output).all (fun co => dotCheck q (input.zip co.1) co.2) = true)
    (i : Fin m) :
    DyadicRectangle.dotCheck p q (fun j => (a j).toDyadic)
      (fun j => (K i j).toDyadic) (b i).toDyadic = true := by
  rw [hK, ho, DyadicRectangle.zip_ofFn] at h
  have hh := List.all_eq_true.mp h (List.ofFn (K i), b i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  exact dotCheck_of_lists a (K i) (b i) input (List.ofFn (K i)) hi rfl hh

end Maxwell.Certificate.DyadicKernel
