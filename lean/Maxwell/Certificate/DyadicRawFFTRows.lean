import Maxwell.Certificate.DyadicRawFFT
import Maxwell.Certificate.DyadicKernelRows
import Maxwell.Certificate.DyadicFFTRows

namespace Maxwell.Certificate.DyadicKernel

def Rectangle.ofFFT : DyadicRectangle → Rectangle
  | ⟨r,i,e⟩ => ⟨r,i,e⟩

@[simp] theorem Rectangle.toDyadic_ofFFT (a : DyadicRectangle) :
    (Rectangle.ofFFT a).toDyadic = a := by cases a; rfl

/-- Exact bindings of the raw lists transport a lightweight arithmetic proof
to the original Fourier interval checker. -/
theorem lineCheck_sound {n m p q : ℕ}
    (a : Fin n → DyadicRectangle) (K : Fin m → Fin n → DyadicRectangle)
    (b : Fin m → DyadicRectangle)
    (input : List Rectangle) (coefficients : List (List Rectangle)) (output : List Rectangle)
    (hi : input = List.ofFn (fun j => Rectangle.ofFFT (a j)))
    (hK : coefficients = List.ofFn (fun i => List.ofFn (fun j => Rectangle.ofFFT (K i j))))
    (ho : output = List.ofFn (fun i => Rectangle.ofFFT (b i)))
    (h : lineCheck q coefficients input output = true) (i : Fin m) :
    DyadicRectangle.dotCheck p q a (K i) (b i) = true := by
  simpa only [Rectangle.toDyadic_ofFFT] using
    line_of_lists (p := p) (q := q) (fun j => Rectangle.ofFFT (a j))
      (fun i j => Rectangle.ofFFT (K i j)) (fun i => Rectangle.ofFFT (b i))
      input coefficients output hi hK ho h i

end Maxwell.Certificate.DyadicKernel
