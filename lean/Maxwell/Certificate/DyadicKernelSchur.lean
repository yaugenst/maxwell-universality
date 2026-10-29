import Maxwell.Certificate.DyadicKernelMagnetic

namespace Maxwell.Certificate.DyadicKernel

def channelDivCheck (p : Nat) (a : Int) (ar : Nat) (b : Int) (br : Nat)
    (c : Int) (cr : Nat) : Bool :=
  let s : Int := 2^p
  decide ((c-cr)*(b-br) ≤ (a-ar)*s ∧ (c-cr)*(b+br) ≤ (a-ar)*s ∧
    (a+ar)*s ≤ (c+cr)*(b-br) ∧ (a+ar)*s ≤ (c+cr)*(b+br))

def divCheck (p : Nat) : Rectangle → Rectangle → Rectangle → Bool
  | ⟨ar,ai,ae⟩,⟨br,_,be⟩,⟨cr,ci,ce⟩ =>
    decide (0 < br-(be:Int)) && channelDivCheck p ar ae br be cr ce &&
      channelDivCheck p ai ae br be ci ce

abbrev Enclosure (n : Nat) := Fin n → Fin n → Rectangle

def schurEntryCheck (p : Nat) (aij ai0 aj0 pivot product quotient result : Rectangle) : Bool :=
  rescaleCheck p (mulExact ai0 (conjugate aj0)) product &&
    divCheck p product pivot quotient && subsetCheck (add aij (neg quotient)) result

inductive SchurProposal : Nat → Type
  | empty : SchurProposal 0
  | next {n : Nat} (enclosure products quotients : Enclosure n)
      (tail : SchurProposal n) : SchurProposal (n+1)

def schurAccepts (p : Nat) : {n : Nat} → Enclosure n → SchurProposal n → Bool
  | 0,_,.empty => true
  | n+1,a,.next b products quotients tail =>
      decide (0 < (a 0 0).re - ((a 0 0).radius : Int)) &&
      decide (∀ i j : Fin n, schurEntryCheck p (a i.succ j.succ)
        (a i.succ 0) (a j.succ 0) (a 0 0) (products i j) (quotients i j) (b i j) = true) &&
      schurAccepts p b tail

end Maxwell.Certificate.DyadicKernel
