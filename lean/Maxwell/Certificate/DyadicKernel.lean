/-! Integer certificate evaluation without analytic imports. Soundness is
proved separately against the existing dyadic rectangle semantics. -/
namespace Maxwell.Certificate.DyadicKernel

structure Rectangle where
  re : Int
  im : Int
  radius : Nat
  deriving DecidableEq

def zero : Rectangle := ⟨0,0,0⟩

def add : Rectangle → Rectangle → Rectangle
  | ⟨ar,ai,ae⟩, ⟨br,bi,be⟩ => ⟨ar+br,ai+bi,ae+be⟩

def conjugate : Rectangle → Rectangle
  | ⟨ar,ai,ae⟩ => ⟨ar,-ai,ae⟩

def mulExact : Rectangle → Rectangle → Rectangle
  | ⟨ar,ai,ae⟩, ⟨br,bi,be⟩ =>
    ⟨ar*br-ai*bi,ar*bi+ai*br,
      (ar.natAbs+ai.natAbs)*be+(br.natAbs+bi.natAbs)*ae+2*ae*be⟩

def dot : List (Rectangle × Rectangle) → Rectangle
  | [] => zero
  | (a,b)::tail => add (mulExact a b) (dot tail)

def rescaleCheck (q : Nat) : Rectangle → Rectangle → Bool
  | ⟨ar,ai,ae⟩, ⟨br,bi,be⟩ =>
    let s : Int := 2^q
    decide ((ar-br*s).natAbs+ae ≤ be*2^q ∧ (ai-bi*s).natAbs+ae ≤ be*2^q)

def dotCheck (q : Nat) (a : List (Rectangle × Rectangle)) (b : Rectangle) : Bool :=
  rescaleCheck q (dot a) b

def subsetCheck : Rectangle → Rectangle → Bool
  | ⟨ar,ai,ae⟩, ⟨br,bi,be⟩ =>
    decide ((ar-br).natAbs+ae ≤ be ∧ (ai-bi).natAbs+ae ≤ be)

def scaleCheck (num den : Int) : Rectangle → Rectangle → Bool
  | ⟨ar,ai,ae⟩, ⟨br,bi,be⟩ =>
    decide (0 < den ∧
      Int.ofNat (ar*num-br*den).natAbs + Int.ofNat ae * Int.ofNat num.natAbs ≤ Int.ofNat be * den ∧
      Int.ofNat (ai*num-bi*den).natAbs + Int.ofNat ae * Int.ofNat num.natAbs ≤ Int.ofNat be * den)

end Maxwell.Certificate.DyadicKernel
