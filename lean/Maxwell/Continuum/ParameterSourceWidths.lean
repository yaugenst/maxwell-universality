import Maxwell.Continuum.ParameterSourceInput
import Maxwell.Continuum.ParameterSourcePrepareCost
import Maxwell.Continuum.ParameterLogWidths
import Maxwell.Continuum.SourceRoutingSourceGeometryWidth

/-! Every source operand used by the actual parameter selector has a
source-uniform logarithmic word bound. -/
noncomputable section
namespace Maxwell.Continuum.Parameters
open Maxwell.Cost Maxwell.Cost.RoutingPorts.Complete Maxwell.Composition
set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

def sourceOperandCoefficient (p : Source.Parameters) : ℕ :=
  40*(⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+11)+2*sourceBudgetExponent p+5

theorem source_operand_width (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hm2 : 2≤S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    SourceInitialize.inputWidth S.n S.nnz (Maxwell.Logical.sourceCircuit S (SelectedInput.input p S hm).precision).size
      (SourcePhase.side S (SelectedInput.input p S hm).precision) (sourceInput p S hm).J+1≤
        sourceOperandCoefficient p*inputLog S.nnz := by
  let n:=(SelectedInput.input p S hm).precision
  let P:=sourceBudgetExponent p
  let ℓ:=inputLog S.nnz
  have input:=sourceInput_binary p S hm hm2 hunit
  have mBits:=sourceBits_le_log S.nnz
  have nBits : S.n.bits.length≤ℓ:=by
    apply (show S.n.bits.length≤S.nnz.bits.length from by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Source.dimension_le_nnz S hunit)).trans
    exact mBits
  have sites : (sourceInput p S hm).J≤2^(P*ℓ):=by
    dsimp only [P,ℓ]
    exact_mod_cast input.J
  have siteBits:=Nat.size_le_size sites
  rw [Nat.size_pow,←Nat.size_eq_bits_len] at siteBits
  have span : (sourceInput p S hm).span 0≤2^(P*ℓ):=by
    dsimp only [P,ℓ]
    exact_mod_cast input.span 0
  have qSmall : SourcePhase.side S n≤(sourceInput p S hm).span 0:=by
    change SourcePhase.side S n≤2^54*129*PhysicalParameters.routingSide S n
    rw [PhysicalParameters.routingSide_eq,SourcePhase.side_eq]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have qBits:=Nat.size_le_size (qSmall.trans span)
  rw [Nat.size_pow,←Nat.size_eq_bits_len] at qBits
  have circuit:=SourcePlan.inputWidth_source S n (Source.dimension_le_nnz S hunit)
  have cBits : (Maxwell.Logical.sourceCircuit S n).size.bits.length≤40*(S.nnz.bits.length+n+1):=by
    apply (show (Maxwell.Logical.sourceCircuit S n).size.bits.length≤SourcePlan.inputWidth S n from by
      change (SourceGraph.Positive.dimension S n).bits.length≤_
      unfold SourcePlan.inputWidth;omega).trans circuit
  have precision : S.nnz.bits.length+n+1≤
      (⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+11)*ℓ:=by
    change S.nnz.bits.length+(7+(⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2)*S.nnz.size)+1≤_
    rw [←Nat.size_eq_bits_len]
    have positive:=inputLog_pos S.nnz
    dsimp only [ℓ] at *
    nlinarith
  have cBound:=cBits.trans (Nat.mul_le_mul_left 40 precision)
  have positive : 1≤ℓ:=inputLog_pos S.nnz
  unfold SourceInitialize.inputWidth sourceOperandCoefficient
  change S.n.bits.length+S.nnz.bits.length+(Maxwell.Logical.sourceCircuit S n).size.bits.length+
    (SourcePhase.side S n).bits.length+(sourceInput p S hm).J.bits.length+1≤_
  dsimp only [P,ℓ] at *
  nlinarith only [nBits,mBits,siteBits,qBits,cBound,positive]

#print axioms source_operand_width
end Maxwell.Continuum.Parameters
