import Maxwell.Cost.MagnitudeMax.Branch
import Maxwell.Cost.MagnitudeMax.BothBound
import Maxwell.Composition.SelectedScaleWidth

/-! The shared parser and base-case test have a source-linear cubic-width
bound, including zero-dimensional and one-entry inputs. -/
noncomputable section
namespace Maxwell.Cost.MagnitudeMax.Branch
open Maxwell.Composition.SelectedScaleWidth
set_option maxHeartbeats 1500000

def coefficient (p : Source.Parameters) : ℕ :=
  13000*(8*inputCoefficient p+12)*((inputCoefficient p+2)^2+4)+13

theorem price_polynomial (p : Source.Parameters) (S : Source.SparseSystem) (hp : Source.Promises p S) :
    price S (inputWidth p S)≤coefficient p*(S.nnz+1)*(unsignedBitLength (2+S.nnz))^3 := by
  let A:=inputCoefficient p
  let ℓ:=unsignedBitLength (2+S.nnz)
  let m:=S.nnz
  let B:=inputWidth p S
  have hℓ : 1≤ℓ:=Maxwell.Realization.inputBitLength_pos S.nnz
  have hw : B≤A*ℓ:=input_width p S
  have hm : unsignedBitLength m≤ℓ:=Codec.unsignedBitLength_mono (by omega)
  have hb : Nat.ceil (Source.bitBudget p S)≤A*ℓ := by
    have small : Nat.ceil (Source.bitBudget p S)≤B := by dsimp [B,inputWidth];omega
    exact small.trans hw
  have length : 3*(2*unsignedBitLength m+1)+
      m*(4*unsignedBitLength m+8*Nat.ceil (Source.bitBudget p S)+4)+1≤(8*A+12)*(m+1)*ℓ := by
    have tail : 4*unsignedBitLength m+8*Nat.ceil (Source.bitBudget p S)+4≤(8*A+8)*ℓ := by
      nlinarith only [hm,hb,hℓ]
    have tail':=Nat.mul_le_mul_left m tail
    nlinarith only [tail',hm,hℓ,Nat.zero_le (A*ℓ)]
  have operand : (B+2)^2+3*unsignedBitLength m+1≤((A+2)^2+4)*ℓ^2 := by
    have raw : B+2≤(A+2)*ℓ := by nlinarith only [hw,hℓ]
    have sq:=Nat.pow_le_pow_left raw 2
    have square : ℓ≤ℓ^2 := by nlinarith only [hℓ]
    nlinarith only [sq,square,hm,hℓ]
  have bounded:=Both.promised_price_le p S hp
  have prod:=Nat.mul_le_mul (Nat.mul_le_mul_left 13000 length) operand
  have total : Both.price S (inputWidth p S)≤
      (13000*(8*A+12)*((A+2)^2+4))*(m+1)*ℓ^3 := by
    exact bounded.trans (prod.trans_eq (by ring))
  have positive : 1≤(m+1)*ℓ^3 := Nat.mul_pos (by omega) (pow_pos hℓ _)
  change Both.price S (inputWidth p S)+13≤_
  change _≤(13000*(8*A+12)*((A+2)^2+4)+13)*(m+1)*ℓ^3
  nlinarith only [total,positive]

#print axioms price_polynomial
end Maxwell.Cost.MagnitudeMax.Branch
