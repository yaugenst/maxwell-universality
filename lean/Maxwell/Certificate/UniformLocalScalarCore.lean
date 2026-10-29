import Maxwell.Certificate.GlobalScalarCore

namespace Maxwell.Certificate.UniformLocalScalar
open ScalarExpression
open GlobalScalar (piUpper sqrtThreeUpper geometryCheck lit plus minus times divide square
  dotExpr smallLowExpr smallHighExpr positiveCheck)
abbrev Proposal := GlobalScalar.Proposal
abbrev Evidence := GlobalScalar.Evidence

def negativeLossExpr (p : Proposal) : Expr :=
  plus (plus (plus (dotExpr p (p.kn 0))
    (times (square (lit p.s)) (plus (times (lit (p.fn 0)) (lit (p.en 0))) (square (lit (p.fn 0))))))
    (divide (times (times (times (lit 2) (lit (1/64))) (square (lit p.s))) (lit p.wn))
      (square (minus (lit 1) (divide (lit p.s) (lit p.r))))))
    (times (lit (1/4096)) (square (lit (p.fn 0))))

def positiveLossExpr (p : Proposal) : Expr :=
  plus (plus (dotExpr p (p.kn 1))
    (times (square (lit p.s)) (plus (times (lit (p.fn 1)) (lit (p.en 1))) (square (lit (p.fn 1))))))
    (times (lit (1/4096)) (square (lit (p.fn 1))))

def gradientLossExpr (p : Proposal) : Expr :=
  plus (divide (times (lit 2) (square (lit p.s))) (square (lit p.r))) (times (lit 64) (lit (1/4096)))

def crossCoefficientExpr (p : Proposal) : Expr :=
  plus (divide (plus (lit 3) (divide (lit p.s) (lit p.r)))
    (square (minus (lit 1) (divide (lit p.s) (lit p.r)))))
    (divide (times (lit (1/2)) (lit p.R)) (minus (lit 1) (divide (lit p.s) (lit p.r))))

def crossExpr (p : Proposal) : Expr :=
  plus (dotExpr p p.crossder) (times (square (lit p.s))
    (plus (times (lit 8) (plus (divide (lit (p.en 1)) (lit 2)) (lit (p.fn 1))))
      (times (times (times (lit 16) (lit (1/64))) (crossCoefficientExpr p)) (lit p.wp2))))

def baseExpr (p : Proposal) : Expr := minus (divide (square (lit p.rh)) (lit 14)) (lit (1/64))
def shiftExpr (p : Proposal) : Expr :=
  minus (minus (divide (square (minus (lit p.rh) (lit p.s))) (lit 14)) (lit (1/64))) (lit (1/4096))
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
    (times (lit (1/4096)) (lit p.qw)))

def gradientResidualExpr (p : Proposal) : Expr :=
  times (chiExpr p) (plus (dotExpr p (p.rhow 1)) (times (square (lit p.s))
    (times (plus (divide (curlmaxExpr p) (lit 2)) (wmaxExpr p)) (lit 8))))

def positiveEtaExpr (p : Proposal) : Expr :=
  plus (square (positiveResidualExpr p))
    (divide (times (times (plus (lit (1/64)) (lit (1/4096))) (square (lit p.s))) (square (lit p.qfn)))
      (square (minus (lit p.rh) (lit p.s))))
def gradientEtaExpr (p : Proposal) : Expr := square (gradientResidualExpr p)

def negativeExpr (p : Proposal) : Expr := minus (lit (1023/1024)) (negativeLossExpr p)
def positiveExpr (p : Proposal) : Expr :=
  minus (minus (lit (1023/1024)) (positiveLossExpr p)) (positiveEtaExpr p)
def gradientExpr (p : Proposal) : Expr := minus (minus (lit 1) (gradientLossExpr p)) (gradientEtaExpr p)
def determinantExpr (p : Proposal) : Expr := minus (times (positiveExpr p) (gradientExpr p))
  (square (plus (crossExpr p) (.sqrt (times (positiveEtaExpr p) (gradientEtaExpr p)))))

def accepts (p : Proposal) (c : Evidence) : Bool :=
  geometryCheck p && (positiveCheck (negativeExpr p) c.negative &&
    (positiveCheck (positiveExpr p) c.positive &&
    (positiveCheck (gradientExpr p) c.gradient &&
    (positiveCheck (determinantExpr p) c.determinant &&
    (positiveCheck (smallLowExpr p) c.smallLow &&
    (positiveCheck (smallHighExpr p) c.smallHigh &&
    (positiveCheck (baseExpr p) c.base && positiveCheck (shiftExpr p) c.shift)))))))


end Maxwell.Certificate.UniformLocalScalar
