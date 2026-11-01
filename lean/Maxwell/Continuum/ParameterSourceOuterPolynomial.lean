import Maxwell.Continuum.ParameterSourceOuterMachine
import Maxwell.Continuum.ParameterOuterPolynomial
import Maxwell.Continuum.ParameterLogWidths

/-! The executed outer search has a source-uniform polylogarithmic cost.
Its raw operand widths follow from the actual source arithmetic and the
already proved binary budget, including the reciprocal error denominator. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourceOuter
open Maxwell.Cost Maxwell.Composition
set_option maxHeartbeats 250000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency true

def operandCoefficient (p : Source.Parameters) (e : ℕ) : ℕ :=
  sourceBudgetExponent p+e+(minimumLengthExponent e).bits.length+3
def sourceWidthCoefficient (p : Source.Parameters) (e : ℕ) : ℕ := 12*operandCoefficient p e
def resourceExponent (p : Source.Parameters) (e : ℕ) : ℕ :=
  4096+e+sourceBudgetExponent p+minimumLengthExponent e
def runtimeCoefficient (p : Source.Parameters) (e : ℕ) : ℕ :=
  OuterMachine.polynomialCoefficient (resourceExponent p e)*(sourceWidthCoefficient p e+2)^60+1

theorem source_value_width (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (hunit : IsUnit (Source.realMatrix S)) (e : ℕ)
    (i : ℕ) (hi : i∈SourcePrepare.ports) :
    (sourceValues p S hm e i).bits.length≤operandCoefficient p e*inputLog S.nnz := by
  let ℓ:=inputLog S.nnz
  let P:=sourceBudgetExponent p
  let C:=operandCoefficient p e
  have positive : 1≤ℓ:=inputLog_pos S.nnz
  have room : P*ℓ+1≤C*ℓ:=by dsimp only [P,C,operandCoefficient];nlinarith
  have small : ℓ≤C*ℓ:=by dsimp only [C,operandCoefficient];nlinarith
  have constants : e+1≤C*ℓ ∧ (minimumLengthExponent e).bits.length≤C*ℓ:=by
    dsimp only [C,operandCoefficient];constructor <;> nlinarith
  have budget:=sourceInput_binary p S hm hm2 hunit
  have natBits (n : ℕ) (h : (n:ℚ)≤(2:ℚ)^(P*ℓ)) : n.bits.length≤C*ℓ:=by
    have bound : n≤2^(P*ℓ):=by exact_mod_cast h
    have bits:=Nat.size_le_size bound
    rw [Nat.size_pow,←Nat.size_eq_bits_len] at bits
    exact bits.trans room
  have mBits:=(sourceBits_le_log S.nnz).trans small
  have jBits:=natBits (sourceInput p S hm).J budget.J
  have k:=budget.K
  rw [source_K_eq] at k
  have kBits:=natBits (sourceBudgetNat p S hm) k
  have eps:=budget.epsilon
  rw [source_epsilon_eq,one_div,inv_inv] at eps
  have epsBits:=natBits (sourceErrorDen p S hm) eps
  have spanBits (j : Fin 3):=((natBits ((sourceInput p S hm).span j) (budget.span j)))
  have hd:=data_initial p S hm hn hm2 e
  change OuterMachine.dataOf (sourceValues p S hm e)=data p S hm e at hd
  have c0:=congrArg OuterMachine.Data.constant hd
  have c1:=congrArg OuterMachine.Data.sourceSize hd
  have c2:=congrArg OuterMachine.Data.wells hd
  have c3:=congrArg OuterMachine.Data.conditionNum hd
  have c4:=congrArg OuterMachine.Data.conditionDen hd
  have c5:=congrArg OuterMachine.Data.epsilonNum hd
  have c6:=congrArg OuterMachine.Data.epsilonDen hd
  have cs (j : Fin 3):=congrArg (fun d:OuterMachine.Data=>d.span j) hd
  have fields:=initial_fields ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S (SelectedInput.input p S hm).precision
  have logBits : (inputLog S.nnz).bits.length≤C*ℓ:=by
    apply (show ℓ.bits.length≤ℓ from by rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self).trans small
  have one : (1:ℕ).bits.length≤C*ℓ:=by change 1≤_;omega
  have power : (2^e).bits.length≤C*ℓ:=by rw [Nat.size_eq_bits_len,Nat.size_pow];exact constants.1
  simp only [SourcePrepare.ports,SourceBudgetMachine.outputs,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl
  · simpa only [sourceValues,fields.2] using constants.2
  · change (sourceValues p S hm e 2210).bits.length≤C*ℓ
    rw [show sourceValues p S hm e 2210=2^e from c0];exact power
  · rw [show sourceValues p S hm e 2211=S.nnz from c1];exact mBits
  · rw [show sourceValues p S hm e 2212=(sourceInput p S hm).J from c2];exact jBits
  · rw [show sourceValues p S hm e 2213=sourceBudgetNat p S hm from c3];exact kBits
  · rw [show sourceValues p S hm e 2214=1 from c4];exact one
  · rw [show sourceValues p S hm e 2215=1 from c5];exact one
  · rw [show sourceValues p S hm e 2216=sourceErrorDen p S hm from c6];exact epsBits
  · rw [show sourceValues p S hm e 2217=(sourceInput p S hm).span 0 from cs 0];exact spanBits 0
  · rw [show sourceValues p S hm e 2218=(sourceInput p S hm).span 1 from cs 1];exact spanBits 1
  · rw [show sourceValues p S hm e 2219=(sourceInput p S hm).span 2 from cs 2];exact spanBits 2
  · simpa only [sourceValues,fields.1] using logBits

theorem source_width_linear (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (hunit : IsUnit (Source.realMatrix S)) (e : ℕ) :
    sourceWidth p S hm e≤sourceWidthCoefficient p e*inputLog S.nnz := by
  unfold sourceWidth inputWidth
  calc
    _≤∑i∈SourcePrepare.ports,operandCoefficient p e*inputLog S.nnz:=by
      apply Finset.sum_le_sum
      intro i hi
      have keep : sourceValues p S hm e i=SourceExecution.values ⌈p.conditionExponent⌉₊
          ⌈p.accuracyExponent⌉₊ e S (SelectedInput.input p S hm).precision i:=by
        simp only [sourceValues,initial,ite_eq_left hi]
      rw [←keep]
      exact source_value_width p S hm hn hm2 hunit e i hi
    _=sourceWidthCoefficient p e*inputLog S.nnz:=by
      rw [Finset.sum_const,Nat.nsmul_eq_mul,show SourcePrepare.ports.card=12 by decide]
      unfold sourceWidthCoefficient
      ring

theorem cost_polynomial (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (hunit : IsUnit (Source.realMatrix S)) (e : ℕ) :
    cost p S hm hn hm2 e≤runtimeCoefficient p e*(inputLog S.nnz)^60 := by
  let v:=sourceValues p S hm e
  let B:=sourceWidth p S hm e
  let M:=resourceExponent p e
  have fields:=initial_fields ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S (SelectedInput.input p S hm).precision
  have data:=data_initial p S hm hn hm2 e
  have input : ((OuterMachine.dataOf v).input (source_positive p S hm hn hm2 e)).BinaryBudget
      (sourceBudgetExponent p) (v 2200):=by
    simpa only [v,sourceValues,data,data_input,fields.1] using sourceInput_binary p S hm hm2 hunit
  have bound:=OuterMachine.polynomial_cost v (source_positive p S hm hn hm2 e) M e
    (sourceBudgetExponent p) B (log_positive p S hm e) input
    (by unfold M resourceExponent;omega) (by unfold M resourceExponent;omega)
    (by unfold M resourceExponent;omega)
    (by dsimp only [v,sourceValues];rw [fields.2];unfold M resourceExponent;omega)
    (fun i _=>initial_width _ _ _ _ _ i)
  have width:=source_width_linear p S hm hn hm2 hunit e
  have positive:=inputLog_pos S.nnz
  have envelope : B+v 2200+1≤(sourceWidthCoefficient p e+2)*inputLog S.nnz:=by
    dsimp only [v,sourceValues]
    rw [fields.1]
    dsimp only [B]
    nlinarith only [width,positive]
  have one : 1≤(inputLog S.nnz)^60:=Nat.one_le_pow _ _ positive
  unfold cost
  calc
    _≤OuterMachine.polynomialCoefficient M*((sourceWidthCoefficient p e+2)*inputLog S.nnz)^60+1:=
      Nat.add_le_add_right (bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left envelope 60))) 1
    _≤runtimeCoefficient p e*(inputLog S.nnz)^60:=by
      rw [mul_pow]
      unfold runtimeCoefficient
      dsimp only [M]
      nlinarith only [one]

#print axioms source_width_linear
#print axioms cost_polynomial
end Maxwell.Continuum.Parameters.SourceOuter
