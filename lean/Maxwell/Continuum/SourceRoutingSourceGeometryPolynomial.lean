import Maxwell.Continuum.SourceRoutingSourceGeometryWidth
import Maxwell.Continuum.ParameterRecords
import Maxwell.Continuum.ParameterLogWidths

/-! The actual source-to-geometry program has the required three-halves
source-size exponent. Its full routing and address charges are included. -/
noncomputable section
namespace Maxwell.Cost.RoutingPorts.Complete.CountedGeometry
open Maxwell.Continuum.Parameters Maxwell.Composition
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024

def sourceWidthCoefficient (p : Source.Parameters) : ℕ :=
  2^25*(⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+11)
def sourceCostCoefficient (p : Source.Parameters) : ℝ :=
  2^708*sharpRoutingCoefficient p*(sourceWidthCoefficient p:ℝ)^4

theorem source_width (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (dimension_le : S.n≤S.nnz)
    (room : SourceGraph.Positive.dimension S (SelectedInput.input p S hm).precision<
      2^SourceGraph.Positive.width S (SelectedInput.input p S hm).precision) :
    wordBound S (SelectedInput.input p S hm).precision room+10≤
      sourceWidthCoefficient p*inputLog S.nnz := by
  have bound:=wordBound_source S (SelectedInput.input p S hm).precision dimension_le room
  have bits:=sourceBits_le_log S.nnz
  have positive:=inputLog_pos S.nnz
  have precision : S.nnz.bits.length+(SelectedInput.input p S hm).precision+1≤
      (⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+11)*inputLog S.nnz:=by
    change S.nnz.bits.length+(7+(⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2)*S.nnz.size)+1≤_
    rw [←Nat.size_eq_bits_len]
    nlinarith
  exact bound.trans ((Nat.mul_le_mul_left (2^25) precision).trans_eq (by
    unfold sourceWidthCoefficient;ring))

theorem source_cost (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hm2 : 2≤S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (room : SourceGraph.Positive.dimension S (SelectedInput.input p S hm).precision<
      2^SourceGraph.Positive.width S (SelectedInput.input p S hm).precision) :
    (cost S (SelectedInput.input p S hm).precision room:ℝ)≤
      sourceCostCoefficient p*(S.nnz:ℝ)^(3/2:ℝ)*(inputLog S.nnz:ℝ)^6 := by
  let n:=(SelectedInput.input p S hm).precision
  let q:=SourcePhase.side S n
  let ℓ:=(inputLog S.nnz:ℝ)
  have width:=source_width p S hm (Source.dimension_le_nnz S hunit) room
  have cube:=source_routing_cube_sharp p S hm hm2 hunit
  change (SourceRouting.side S n:ℝ)^3≤_ at cube
  rw [←SourcePhase.side_eq] at cube
  change (q:ℝ)^3≤sharpRoutingCoefficient p*(S.nnz:ℝ)^(3/2:ℝ)*ℓ^(3/2:ℝ) at cube
  have side : 1≤q:=SourcePhase.side_pos S n
  have sideR : (1:ℝ)≤q:=by exact_mod_cast side
  have enlarged : ((q+1:ℕ):ℝ)^3≤8*(q:ℝ)^3:=by
    have h:=pow_le_pow_left₀ (by positivity : (0:ℝ)≤q+1)
      (show (q:ℝ)+1≤2*q by linarith) 3
    push_cast
    nlinarith only [h]
  have log : (1:ℝ)≤ℓ:=by
    dsimp only [ℓ]
    exact_mod_cast (show 1≤ inputLog S.nnz from inputLog_pos S.nnz)
  have logPower : ℓ^(3/2:ℝ)≤ℓ^2:=by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le log
      (by norm_num : (3/2:ℝ)≤2)
  have words : ((wordBound S n room+10:ℕ):ℝ)≤(sourceWidthCoefficient p:ℝ)*ℓ:=by
    dsimp only [n,ℓ]
    exact_mod_cast width
  have charge : (cost S n room:ℝ)≤2^705*((q+1:ℕ):ℝ)^3*
      ((wordBound S n room+10:ℕ):ℝ)^4:=by exact_mod_cast cost_bound S n room
  have coefficient:=sharpRoutingCoefficient_nonneg p
  calc
    _≤2^705*((q+1:ℕ):ℝ)^3*((wordBound S n room+10:ℕ):ℝ)^4:=charge
    _≤2^705*(8*(sharpRoutingCoefficient p*(S.nnz:ℝ)^(3/2:ℝ)*ℓ^2))*
        ((sourceWidthCoefficient p:ℝ)*ℓ)^4:=by
      gcongr
      exact enlarged.trans (mul_le_mul_of_nonneg_left
        (cube.trans (mul_le_mul_of_nonneg_left logPower (by positivity))) (by norm_num))
    _=_:=by unfold sourceCostCoefficient;dsimp only [ℓ];ring

#print axioms source_cost
end Maxwell.Cost.RoutingPorts.Complete.CountedGeometry
