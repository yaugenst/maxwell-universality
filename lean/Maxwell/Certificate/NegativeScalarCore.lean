import Maxwell.Certificate.GlobalScalarCore

namespace Maxwell.Certificate.NegativeScalar

open ScalarExpression GlobalScalar

/-- Only data used by the original material's two negative trial columns. -/
structure Proposal where
  half : ℚ
  s : ℚ
  r : ℚ
  fn : ℚ
  en : ℚ
  kn : Fin 3 → ℚ
  wn : ℚ

def geometryCheck (p : Proposal) : Bool := decide
  (0 ≤ p.half ∧ 0 ≤ p.s ∧
    piUpper/10*(sqrtThreeUpper*p.half) ≤ p.s)

def dotExpr (p : Proposal) : Expr :=
  plus (plus (times (lit p.half) (lit (p.kn 0)))
    (times (lit p.half) (lit (p.kn 1)))) (times (lit p.half) (lit (p.kn 2)))

/-- The exact loss formula at frequency half-width `1/4096`. -/
def lossExpr (p : Proposal) : Expr :=
  plus (plus (plus (dotExpr p)
    (times (square (lit p.s))
      (plus (times (lit p.fn) (lit p.en)) (square (lit p.fn)))))
    (divide (times (times (times (lit 2) (lit (1/64))) (square (lit p.s))) (lit p.wn))
      (square (minus (lit 1) (divide (lit p.s) (lit p.r))))))
    (times (lit (1/4096)) (square (lit p.fn)))

def marginExpr (p : Proposal) : Expr := minus (lit (1023/1024)) (lossExpr p)
def smallExpr (p : Proposal) : Expr := minus (lit p.r) (lit p.s)

structure Evidence where
  margin : ScalarExpression.Certificate
  small : ScalarExpression.Certificate

def accepts (p : Proposal) (e : Evidence) : Bool :=
  geometryCheck p && (positiveCheck (marginExpr p) e.margin &&
    positiveCheck (smallExpr p) e.small)

structure VerifiedProposal where
  proposal : Proposal
  evidence : Evidence
  checked : accepts proposal evidence = true

end Maxwell.Certificate.NegativeScalar
