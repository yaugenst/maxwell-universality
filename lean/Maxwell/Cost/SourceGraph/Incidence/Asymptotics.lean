import Maxwell.Cost.SourceGraph.Incidence
import Maxwell.Cost.SourceGraph.Asymptotics
import Maxwell.Cost.GraphIncidence.Width

/-! Actual source parsing, graph construction, and incidence counting have
one uniform source-linear polylogarithmic running-time bound. -/
namespace Maxwell.Cost.SourceGraph.Incidence
open Maxwell.Cost.SourceGraph.Positive SourceCircuit RationalAccumulator
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def incidenceFactor : ℕ := 400000*73*200^2
def totalFactor : ℕ := graphFactor+incidenceFactor

theorem phaseBudget_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    phaseBudget S (Realization.binaryCoefficientPrecision S.nnz k c)≤
      incidenceFactor*((Codec.source S).length+S.nnz+1)*(NormalizeSource.frontendWidth p S k c+1)^3 := by
  let m:=S.nnz
  let P:=Realization.binaryCoefficientPrecision m k c
  let F:=NormalizeSource.frontendWidth p S k c+1
  let N:=(Codec.source S).length+m+1
  let d:=dimension S P
  let e:=count S P
  let w:=width S P
  have bitSize : m.bits.length≤F:=by
    dsimp [F,NormalizeSource.frontendWidth,m]
    simp only [Nat.size_eq_bits_len]
    nlinarith
  have precision : P+1≤F:=by dsimp [P,F,Realization.binaryCoefficientPrecision,NormalizeSource.frontendWidth,m];nlinarith
  have positive : 1≤F:=by dsimp only [F];omega
  have countN : m≤N:=by dsimp only [N];omega
  have source:=Logical.sourceCircuit_size S P (Source.dimension_le_nnz S hp.1)
  change d≤6*m*(P+1) at source
  have edges:=Logical.sourceSquareEntries_length_le S P
  change e≤3*d at edges
  have dimensions : 4*e+1≤73*N*F:=by
    have h:=Nat.mul_le_mul countN precision
    have npos : 1≤N:=by dsimp only [N];omega
    have prod:=Nat.mul_le_mul npos positive
    nlinarith only [h,source,edges,prod]
  have pBits : P.bits.length≤P:=by rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have pSuccBits : (P+1).bits.length≤P+1:=by rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have a:=bits_mul_le 6 m
  have b:=bits_mul_le (6*m) (P+1)
  have dBits : d.bits.length≤(6*m*(P+1)).bits.length:=by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size source
  have eBits : e.bits.length≤(3*d).bits.length:=by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size edges
  have times:=bits_mul_le 3 d
  simp only [show (6:ℕ).bits.length=3 by decide] at a
  simp only [show (3:ℕ).bits.length=2 by decide] at times
  have large : 30≤F:=by dsimp [F,NormalizeSource.frontendWidth];nlinarith
  have descriptor:=GraphIncidence.descriptor_width w d e
  have wide : IncidencePass.budget (GraphIncidence.layout w d e) (4*e).bits+(w+3)+6≤200*F:=by
    have sharper : w+d.bits.length+e.bits.length+10≤10*F:=by
      dsimp only [w,width,InitializeMetadata.width,InitializeMetadata.exponent]
      simp only [←Nat.size_eq_bits_len]
      dsimp only [m,P,d,e] at *
      omega
    exact descriptor.trans (by omega)
  unfold phaseBudget
  change 400000*(4*e+1)*(IncidencePass.budget (GraphIncidence.layout w d e) (4*e).bits+(w+3)+5+1)^2≤_
  calc
    _≤400000*(73*N*F)*(200*F)^2:=Nat.mul_le_mul (Nat.mul_le_mul_left _ dimensions)
      (Nat.pow_le_pow_left (by omega) 2)
    _=incidenceFactor*N*F^3:=by unfold incidenceFactor;ring

theorem totalBudget_bound (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (k c : ℕ) :
    totalBudget p S k c≤totalFactor*((Codec.source S).length+S.nnz+1)*
      (NormalizeSource.frontendWidth p S k c+1)^3 := by
  have a:=Positive.totalBudget_bound p S hp k c
  have b:=phaseBudget_bound p S hp k c
  unfold totalBudget totalFactor
  nlinarith only [a,b]

#print axioms totalBudget_bound

noncomputable def runtimeFactor (p : Source.Parameters) (k c : ℕ) : ℝ :=
  totalFactor*SourceSquare.sourceLogFactor p*(SourceSquare.widthLogFactor p k c)^3

theorem runtimeFactor_nonneg (p : Source.Parameters) (k c : ℕ) : 0≤runtimeFactor p k c := by
  have := SourceSquare.logUnit_pos
  have := p.inputBitFactor_pos
  unfold runtimeFactor SourceSquare.sourceLogFactor SourceSquare.widthLogFactor
  positivity

theorem totalBudget_polylog (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2≤S.nnz) (k c : ℕ) :
    (totalBudget p S k c:ℝ)≤runtimeFactor p k c*(S.nnz:ℝ)*Real.log ((S.nnz:ℝ)+2)^4 := by
  have length:=SourceSquare.sourceLength_log_bound p S hp hm
  have width:=SourceSquare.frontendWidth_log_bound p S k c hm
  have widthPow:=pow_le_pow_left₀
    (Nat.cast_nonneg (NormalizeSource.frontendWidth p S k c+1)) width 3
  have lengthNonneg : 0≤SourceSquare.sourceLogFactor p*(S.nnz:ℝ)*Real.log ((S.nnz:ℝ)+2):=
    (Nat.cast_nonneg ((Codec.source S).length+S.nnz+1)).trans length
  have product:=mul_le_mul length widthPow (by positivity) lengthNonneg
  have scale:=mul_le_mul_of_nonneg_left product (Nat.cast_nonneg totalFactor (α:=ℝ))
  have charge : (totalBudget p S k c:ℝ)≤(totalFactor:ℝ)*
      (((Codec.source S).length+S.nnz+1:ℕ):ℝ)*((NormalizeSource.frontendWidth p S k c+1:ℕ):ℝ)^3:=by
    exact_mod_cast totalBudget_bound p S hp k c
  apply charge.trans
  convert scale using 1 <;> (try unfold runtimeFactor) <;> ring

#print axioms totalBudget_polylog
end Maxwell.Cost.SourceGraph.Incidence
