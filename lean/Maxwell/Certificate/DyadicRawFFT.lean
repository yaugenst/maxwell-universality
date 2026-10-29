import Maxwell.Certificate.DyadicKernel

namespace Maxwell.Certificate.DyadicKernel

/-- All outputs of a literal Fourier line, evaluated without analytic imports. -/
def lineCheck (q : Nat) (coefficients : List (List Rectangle))
    (input output : List Rectangle) : Bool :=
  (coefficients.zip output).all fun co => dotCheck q (input.zip co.1) co.2

end Maxwell.Certificate.DyadicKernel
