import Maxwell.Certificate.DyadicListRows

/-! Sequential list checks avoid repeated lookup through the three cell indices.
Every input, coefficient, and output list is bound to its finite matrix data. -/
namespace Maxwell.Certificate.DyadicRectangle

def lineCheck (p q : ℕ) (input : List DyadicRectangle)
    (coefficients : List (List DyadicRectangle)) (output : List DyadicRectangle) : Bool :=
  (coefficients.zip output).all fun kc => listDotCheck p q (input.zip kc.1) kc.2

theorem lineCheck_sound {m n p q : ℕ} {a : Fin n → DyadicRectangle}
    {K : Fin m → Fin n → DyadicRectangle} {b : Fin m → DyadicRectangle}
    {input output : List DyadicRectangle} {coefficients : List (List DyadicRectangle)}
    (ha : input = List.ofFn a) (hK : coefficients = List.ofFn (fun k => List.ofFn (K k)))
    (hb : output = List.ofFn b) (h : lineCheck p q input coefficients output = true) :
    ∀ k, dotCheck p q a (K k) (b k) = true := by
  rw [lineCheck, hK, hb, zip_ofFn] at h
  have hh : ∀ k, listDotCheck p q (input.zip (List.ofFn (K k))) (b k) = true := by
    simpa only [List.all_eq_true, List.forall_mem_ofFn_iff] using h
  intro k
  exact dotCheck_of_zip ha rfl (hh k)

abbrev LineData := List DyadicRectangle × List DyadicRectangle

def batchCheck (p q : ℕ) (coefficients : List (List DyadicRectangle))
    (rows : List (List LineData)) : Bool :=
  rows.all fun block => block.all fun io => lineCheck p q io.1 coefficients io.2

theorem batchCheck_sound {l t m n p q : ℕ}
    {a : Fin l → Fin t → Fin n → DyadicRectangle}
    {b : Fin l → Fin t → Fin m → DyadicRectangle}
    {K : Fin m → Fin n → DyadicRectangle}
    {rows : List (List LineData)} {coefficients : List (List DyadicRectangle)}
    (hr : rows = List.ofFn (fun i => List.ofFn (fun j =>
      (List.ofFn (a i j), List.ofFn (b i j)))))
    (hK : coefficients = List.ofFn (fun k => List.ofFn (K k)))
    (h : batchCheck p q coefficients rows = true) :
    ∀ i j k, dotCheck p q (a i j) (K k) (b i j k) = true := by
  rw [batchCheck, hr] at h
  have hh : ∀ i j,
      lineCheck p q (List.ofFn (a i j)) coefficients (List.ofFn (b i j)) = true := by
    simpa only [List.all_eq_true, List.forall_mem_ofFn_iff] using h
  intro i j k
  exact lineCheck_sound rfl hK rfl (hh i j) k

def blockCheck (p q : ℕ) (coefficients : List (List DyadicRectangle))
    (block : List LineData) : Bool :=
  block.all fun io => lineCheck p q io.1 coefficients io.2

theorem batchCheck_of_blocks {l p q : ℕ} {coefficients : List (List DyadicRectangle)}
    (blocks : Fin l → List LineData)
    (h : ∀ i, blockCheck p q coefficients (blocks i) = true) :
    batchCheck p q coefficients (List.ofFn blocks) = true := by
  simpa only [blockCheck, batchCheck, List.all_eq_true, List.forall_mem_ofFn_iff] using h

end Maxwell.Certificate.DyadicRectangle
