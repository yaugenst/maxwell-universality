import Maxwell.Certificate.DyadicKernelSchur

namespace Maxwell.Certificate.DyadicKernel

/-- Floor the two centers at the new scale. Two additional units cover both
the old radius remainder and the center rounding remainder. -/
def round (q : Nat) : Rectangle → Rectangle
  | ⟨r,i,e⟩ =>
    let s : Nat := 2^q
    ⟨r/(s:Int),i/(s:Int),e/s+2⟩

def mulRound (p : Nat) (a b : Rectangle) : Rectangle := round p (mulExact a b)

def dotRound (q : Nat) (pairs : List (Rectangle × Rectangle)) : Rectangle :=
  round q (dot pairs)

def lowerQuotient (p : Nat) (c : Int) (r : Nat) (b : Int) (s : Nat) : Int :=
  min (((c-r)*2^p)/(b-s)) (((c-r)*2^p)/(b+s))

def upperQuotient (p : Nat) (c : Int) (r : Nat) (b : Int) (s : Nat) : Int :=
  max (-((-(c+r)*2^p)/(b-s))) (-((-(c+r)*2^p)/(b+s)))

def centerRadius (lo hi : Int) : Int × Nat :=
  let c := (lo+hi)/2
  (c,max (c-lo).natAbs (hi-c).natAbs)

/-- A deterministic outward real-interval division. The positive denominator
test is part of the function, so unsuccessful inputs produce no rectangle. -/
def divRound (p : Nat) : Rectangle → Rectangle → Option Rectangle
  | ⟨ar,ai,ae⟩,⟨br,_,be⟩ =>
    if 0 < br-(be:Int) then
      let r := centerRadius (lowerQuotient p ar ae br be) (upperQuotient p ar ae br be)
      let i := centerRadius (lowerQuotient p ai ae br be) (upperQuotient p ai ae br be)
      some ⟨r.1,i.1,max r.2 i.2⟩
    else none

end Maxwell.Certificate.DyadicKernel
