import Maxwell.Continuum.ParameterSourceSelected
import Maxwell.Continuum.ParameterSourceOuterPolynomial
import Maxwell.Continuum.ParameterSourcePreparePolynomial
import Maxwell.Continuum.SourceRoutingSourceGeometryPolynomial
import Maxwell.Cost.SourceGraph.Incidence.Asymptotics
import Maxwell.Composition.SelectedScaleWidth

/-! The complete source-to-selected-parameters machine is bounded uniformly
on every input and every random tape. No branch has consumed randomness yet. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourceSelected
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RoutingPorts.Complete Maxwell.Composition
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

def runtimeCoefficient (p : Source.Parameters) (e : ℕ) : ℝ :=
  SourceGraph.Incidence.runtimeFactor p ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊+
    CountedGeometry.sourceCostCoefficient p+SourcePrepare.sourceCostCoefficient p e+
    SourceOuter.runtimeCoefficient p e

theorem complete_cost (p : Source.Parameters) (S : Source.SparseSystem) (hp : Source.Promises p S)
    (hm : 0<S.nnz) (hn : 0<S.n) (hm2 : 2≤S.nnz) (e : ℕ)
    (room : SourceGraph.Positive.dimension S (SelectedInput.input p S hm).precision<
      2^SourceGraph.Positive.width S (SelectedInput.input p S hm).precision) :
    ((SourceGraph.Incidence.totalBudget p S ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊+
      SourceExecution.cost ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S
        (SelectedInput.input p S hm).precision room+SourceOuter.cost p S hm hn hm2 e:ℕ):ℝ)≤
      runtimeCoefficient p e*(S.nnz:ℝ)^(3/2:ℝ)*(inputLog S.nnz:ℝ)^60 := by
  let ℓ:=(inputLog S.nnz:ℝ)
  let μ:=(S.nnz:ℝ)^(3/2:ℝ)
  have lm : (1:ℝ)≤S.nnz:=by exact_mod_cast hm
  have ll : 1≤ℓ:=by dsimp only [ℓ];exact_mod_cast (show 1≤ inputLog S.nnz from inputLog_pos S.nnz)
  have mass : (S.nnz:ℝ)≤μ:=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le lm
      (by norm_num : (1:ℝ)≤3/2)
  have oneMass : 1≤μ:=lm.trans mass
  have logBound : Real.log ((S.nnz:ℝ)+2)≤ℓ:=by
    have a:=SelectedScaleWidth.log_le_inputBits S.nnz
    have b : (unsignedBitLength (2+S.nnz):ℝ)≤ℓ:=by dsimp only [ℓ];exact_mod_cast inputBits_le_log S.nnz
    simpa only [add_comm] using a.trans b
  have logPositive : 0≤Real.log ((S.nnz:ℝ)+2):=Real.log_nonneg (by linarith only [lm])
  have inputCost:=SourceGraph.Incidence.totalBudget_polylog p S hp hm2
    ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊
  have inputCoeff:=SourceGraph.Incidence.runtimeFactor_nonneg p ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊
  have inc : (SourceGraph.Incidence.totalBudget p S ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊:ℝ)≤
      SourceGraph.Incidence.runtimeFactor p ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊*μ*ℓ^60:=by
    apply inputCost.trans
    have logs : Real.log ((S.nnz:ℝ)+2)^4≤ℓ^60:=
      (pow_le_pow_left₀ logPositive logBound 4).trans (pow_le_pow_right₀ ll (by decide))
    gcongr
  have geometryCost:=CountedGeometry.source_cost p S hm hm2 hp.1 room
  have geometryCoeff : 0≤CountedGeometry.sourceCostCoefficient p:=by
    have := sharpRoutingCoefficient_nonneg p
    unfold CountedGeometry.sourceCostCoefficient
    positivity
  have geometry : (CountedGeometry.cost S (SelectedInput.input p S hm).precision room:ℝ)≤
      CountedGeometry.sourceCostCoefficient p*μ*ℓ^60:=by
    apply geometryCost.trans
    gcongr
    norm_num
  have pure (A cost k : ℕ) (hk : k≤60) (hc : cost≤A*(inputLog S.nnz)^k) :
      (cost:ℝ)≤(A:ℝ)*μ*ℓ^60:=by
    have charge : (cost:ℝ)≤(A:ℝ)*ℓ^k:=by dsimp only [ℓ];exact_mod_cast hc
    calc
      _≤(A:ℝ)*ℓ^k:=charge
      _≤((A:ℝ)*μ)*ℓ^60:=by
        apply mul_le_mul
        · exact le_mul_of_one_le_right (Nat.cast_nonneg A) oneMass
        · exact pow_le_pow_right₀ ll hk
        · positivity
        · positivity
  have prep:=pure _ _ 2 (by decide) (SourcePrepare.source_cost p S hm hm2 hp.1 e)
  dsimp only [sourceInput] at prep
  have outer:=pure _ _ 60 le_rfl (SourceOuter.cost_polynomial p S hm hn hm2 hp.1 e)
  unfold SourceExecution.cost
  push_cast
  dsimp only [runtimeCoefficient]
  change _≤(SourceGraph.Incidence.runtimeFactor p ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊+
    CountedGeometry.sourceCostCoefficient p+(SourcePrepare.sourceCostCoefficient p e:ℝ)+
    (SourceOuter.runtimeCoefficient p e:ℝ))*μ*ℓ^60
  nlinarith only [inc,geometry,prep,outer]

theorem executes_polylog (p : Source.Parameters) (S : Source.SparseSystem) (hp : Source.Promises p S)
    (hm2 : 2≤S.nnz) (hb : S.source≠0) (e : ℕ) (tape : ℕ→Bool) :
    ∃steps t,Executes (Codec.source S) tape (code ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e)
      steps (Store.ofState BitRAMState.initial) t ∧
      (steps:ℝ)≤runtimeCoefficient p e*(S.nnz:ℝ)^(3/2:ℝ)*(inputLog S.nnz:ℝ)^60 ∧
      Result p S (by omega) (Source.dimension_pos_of_source_ne_zero S hb) hm2 e t := by
  obtain ⟨room,steps,t,execution,cost,result⟩:=executes p S hp hm2 hb e tape
  refine ⟨steps,t,execution,?_,result⟩
  apply (le_trans ?_ (complete_cost p S hp (by omega) (Source.dimension_pos_of_source_ne_zero S hb) hm2 e room))
  exact_mod_cast cost

#print axioms executes_polylog
end Maxwell.Continuum.Parameters.SourceSelected
