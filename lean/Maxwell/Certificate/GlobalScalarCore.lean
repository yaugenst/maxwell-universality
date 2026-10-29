import Maxwell.Certificate.ScalarExpression
import Mathlib.Data.Fin.VecNotation

namespace Maxwell.Certificate.GlobalScalar

open ScalarExpression

/-- Exact rational values of the frozen scalar proposals. `s` and `R` are
outward rational upper bounds for the box radius and low-symbol cutoff. -/
structure Proposal where
  half : ℚ
  s : ℚ
  r : ℚ
  rh : ℚ
  R : ℚ
  cutoff : ℚ
  fn : Fin 2 → ℚ
  en : Fin 2 → ℚ
  kn : Fin 2 → Fin 3 → ℚ
  crossder : Fin 3 → ℚ
  rhow : Fin 2 → Fin 3 → ℚ
  wn : ℚ
  wp2 : ℚ
  qfn : ℚ
  qw : ℚ
  rzero : ℚ

def piUpper : ℚ := 314159265358979323847/10^20
def sqrtThreeUpper : ℚ := 173205080756887729353/10^20

/-- Geometry checks are rational; their real norm consequence is proved in
`GlobalScalar`. -/
def geometryCheck (p : Proposal) : Bool := decide
  (0 ≤ p.half ∧ 0 ≤ p.s ∧ 0 ≤ p.R ∧
    piUpper/10*(sqrtThreeUpper*p.half) ≤ p.s ∧ p.cutoff ≤ p.R^2)

def lit (q : ℚ) : Expr := .rat q
def plus (a b : Expr) : Expr := .add a b
def minus (a b : Expr) : Expr := .sub a b
def times (a b : Expr) : Expr := .mul a b
def divide (a b : Expr) : Expr := .mul a (.inv b)
def square (a : Expr) : Expr := .mul a a

def dotExpr (p : Proposal) (v : Fin 3 → ℚ) : Expr :=
  plus (plus (times (lit p.half) (lit (v 0))) (times (lit p.half) (lit (v 1))))
    (times (lit p.half) (lit (v 2)))

def negativeLossExpr (p : Proposal) : Expr :=
  plus (plus (plus (dotExpr p (p.kn 0))
    (times (square (lit p.s)) (plus (times (lit (p.fn 0)) (lit (p.en 0))) (square (lit (p.fn 0))))))
    (divide (times (times (times (lit 2) (lit (1/64))) (square (lit p.s))) (lit p.wn))
      (square (minus (lit 1) (divide (lit p.s) (lit p.r))))))
    (times (lit (1/2^24)) (square (lit (p.fn 0))))

def positiveLossExpr (p : Proposal) : Expr :=
  plus (plus (dotExpr p (p.kn 1))
    (times (square (lit p.s)) (plus (times (lit (p.fn 1)) (lit (p.en 1))) (square (lit (p.fn 1))))))
    (times (lit (1/2^24)) (square (lit (p.fn 1))))

def gradientLossExpr (p : Proposal) : Expr :=
  plus (divide (times (lit 2) (square (lit p.s))) (square (lit p.r))) (times (lit 64) (lit (1/2^24)))

def crossCoefficientExpr (p : Proposal) : Expr :=
  plus (divide (plus (lit 3) (divide (lit p.s) (lit p.r)))
    (square (minus (lit 1) (divide (lit p.s) (lit p.r)))))
    (divide (times (lit (1/2)) (lit p.R)) (minus (lit 1) (divide (lit p.s) (lit p.r))))

def crossExpr (p : Proposal) : Expr :=
  plus (dotExpr p p.crossder) (times (square (lit p.s))
    (plus (times (lit 8) (plus (divide (lit (p.en 1)) (lit 2)) (lit (p.fn 1))))
      (times (times (times (lit 16) (lit (1/64))) (crossCoefficientExpr p)) (lit p.wp2))))

def baseExpr (p : Proposal) : Expr := minus (divide (square (lit p.rh)) (lit 13)) (lit (1/64))
def shiftExpr (p : Proposal) : Expr :=
  minus (minus (divide (square (minus (lit p.rh) (lit p.s))) (lit 13)) (lit (1/64))) (lit (1/2^24))
def wmaxExpr (p : Proposal) : Expr := .inv (.sqrt (baseExpr p))
def curlmaxExpr (p : Proposal) : Expr := divide (lit p.rh) (.sqrt (baseExpr p))
def chiExpr (p : Proposal) : Expr := .sqrt (divide (baseExpr p) (shiftExpr p))
def projectorCoefficientExpr (p : Proposal) : Expr :=
  divide (plus (plus (divide (lit p.rh) (lit 2)) (lit 3)) (divide (lit p.s) (lit p.rh)))
    (square (minus (lit p.rh) (lit p.s)))

def positiveResidualExpr (p : Proposal) : Expr :=
  times (chiExpr p) (plus (plus (plus (times (wmaxExpr p) (lit p.rzero)) (dotExpr p (p.rhow 0)))
    (times (square (lit p.s))
      (plus (plus (divide (times (wmaxExpr p) (lit (p.en 1))) (lit 2))
        (times (plus (divide (curlmaxExpr p) (lit 2)) (wmaxExpr p)) (lit (p.fn 1))))
        (times (times (times (times (lit 2) (lit (1/64))) (wmaxExpr p))
          (projectorCoefficientExpr p)) (lit p.qfn)))))
    (times (lit (1/2^24)) (lit p.qw)))

def gradientResidualExpr (p : Proposal) : Expr :=
  times (chiExpr p) (plus (dotExpr p (p.rhow 1)) (times (square (lit p.s))
    (times (plus (divide (curlmaxExpr p) (lit 2)) (wmaxExpr p)) (lit 8))))

def positiveEtaExpr (p : Proposal) : Expr :=
  plus (square (positiveResidualExpr p))
    (divide (times (times (plus (lit (1/64)) (lit (1/2^24))) (square (lit p.s))) (square (lit p.qfn)))
      (square (minus (lit p.rh) (lit p.s))))
def gradientEtaExpr (p : Proposal) : Expr := square (gradientResidualExpr p)

def negativeExpr (p : Proposal) : Expr := minus (lit (1023/1024)) (negativeLossExpr p)
def positiveExpr (p : Proposal) : Expr :=
  minus (minus (lit (1023/1024)) (positiveLossExpr p)) (positiveEtaExpr p)
def gradientExpr (p : Proposal) : Expr := minus (minus (lit 1) (gradientLossExpr p)) (gradientEtaExpr p)
def determinantExpr (p : Proposal) : Expr := minus (times (positiveExpr p) (gradientExpr p))
  (square (plus (crossExpr p) (.sqrt (times (positiveEtaExpr p) (gradientEtaExpr p)))))

def smallLowExpr (p : Proposal) : Expr := minus (lit p.r) (lit p.s)
def smallHighExpr (p : Proposal) : Expr := minus (lit p.rh) (lit p.s)

/-- Eight root certificates, in the order emitted by the scalar verifier. -/
structure Evidence where
  negative : ScalarExpression.Certificate
  positive : ScalarExpression.Certificate
  gradient : ScalarExpression.Certificate
  determinant : ScalarExpression.Certificate
  smallLow : ScalarExpression.Certificate
  smallHigh : ScalarExpression.Certificate
  base : ScalarExpression.Certificate
  shift : ScalarExpression.Certificate

def positiveCheck (e : Expr) (c : ScalarExpression.Certificate) : Bool :=
  verifyExpr e c && Interval.lowerCheck c.interval 0

def accepts (p : Proposal) (c : Evidence) : Bool :=
  geometryCheck p && (positiveCheck (negativeExpr p) c.negative &&
    (positiveCheck (positiveExpr p) c.positive &&
    (positiveCheck (gradientExpr p) c.gradient &&
    (positiveCheck (determinantExpr p) c.determinant &&
    (positiveCheck (smallLowExpr p) c.smallLow &&
    (positiveCheck (smallHighExpr p) c.smallHigh &&
    (positiveCheck (baseExpr p) c.base && positiveCheck (shiftExpr p) c.shift)))))))


/-- A finite rational proposal together with its checked arithmetic witness. -/
structure VerifiedProposal where
  proposal : Proposal
  evidence : Evidence
  checked : accepts proposal evidence = true

end Maxwell.Certificate.GlobalScalar
