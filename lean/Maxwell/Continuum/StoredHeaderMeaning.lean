import Maxwell.Continuum.StoredHeaderMachine
import Maxwell.Continuum.StoredAmbientPhysical
import Maxwell.Continuum.ContinuumDescription

/-! Identify every field emitted by the runtime header with the exact
continuum instance and its sampled dyadic perturbation. -/
noncomputable section
namespace Maxwell.Continuum.StoredHeader
open Maxwell.Cost Maxwell.Cost.Structured RealizationParameters
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude MasterConstants.exponent

theorem prepared_residual {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
    {v : ℕ→ℕ} (h : DecoderSelectors.Inputs p S hm v)
    (epsilon : v 2216=Parameters.sourceErrorDen p S hm) :
    prepared v 730=residualDenominator p S hm := by
  have radiusEq:=h.radius_eq
  change (1:ℚ)/(v 2237)=1/(2:ℚ)^Parameters.tauBits
    (length p S hm) (spacing p S hm) (length_pos p S hm) at radiusEq
  have denominator : (v 2237:ℚ)=(2:ℚ)^Parameters.tauBits
      (length p S hm) (spacing p S hm) (length_pos p S hm) := by
    apply inv_injective
    simpa only [one_div] using radiusEq
  have natural : v 2237=2^Parameters.tauBits
      (length p S hm) (spacing p S hm) (length_pos p S hm) := by exact_mod_cast denominator
  rw [(prepared_fraction v).1,h.nonzeros,h.spectral,epsilon,natural]
  rfl

theorem bits_physical {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
    (j : Fin (drawCount p S hm)) (energyPort : ℕ) (energyLower : 733 ≤ energyPort)
    (v : ℕ→ℕ) (h : DecoderSelectors.Inputs p S hm v)
    (dimension : v 500=S.n) (source : v 4427=sourcePrecision p S)
    (epsilon : v 2216=Parameters.sourceErrorDen p S hm)
    (integer : v 4701=(gridReportFormat p S hm).integerBits)
    (fractional : v 4702=momentPrecision p S)
    (energyValue : ((v energyPort:ℚ)-v (energyPort+1))/v (energyPort+2)=energy p S hm)
    (normalization : (v 4707:ℚ)/v 4708=normalizationScale S)
    (precision : v 4506=detuningPrecision p S hm) (numerator : v 4510=2*j.val+1) :
    bits energyPort v=headerBits p S hm j := by
  have high (i : ℕ) (hi : 733 ≤ i) : prepared v i=v i := prepared_kept v i (by
    simp only [outputs,outputList,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    omega)
  have naturalBits : StoredNatural.bits StoredNatural.continuumHeaderPorts (prepared v)=
      (headerNats p S hm).flatMap Codec.nat := by
    have fields:=prepared_nats v
    rw [dimension,h.nonzeros,StoredAmbient.side_physical h 0,StoredAmbient.side_physical h 1,
      StoredAmbient.side_physical h 2,source,h.moment,integer,fractional] at fields
    have last : (gridReportFormat p S hm).integerBits+momentPrecision p S+1=
        FiniteAuxiliary.messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+3 := by
      change (_+2)+_+1=_
      omega
    rw [last] at fields
    change StoredNatural.continuumHeaderPorts.flatMap (fun i=>Codec.nat (prepared v i))=_
    rw [←List.flatMap_map,fields]
    rfl
  have residualValue : (1:ℚ)/prepared v 730=residual p S hm := by
    rw [prepared_residual h epsilon,residual_reciprocal]
    exact one_div _
  have detuning : Codec.nat (v 4506)++Codec.int (v 4510:ℤ)=detuningBits p S hm j := by
    rw [precision,numerator]
    simp [detuningBits,detuningData]
  unfold bits
  rw [naturalBits,detuning]
  unfold RationalCanonical.StoredEmission.listBits fractions
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,
    high energyPort energyLower,high (energyPort+1) (by omega),high (energyPort+2) (by omega),
    high 4707 (by decide),high 4708 (by decide),(prepared_fraction v).2.1,(prepared_fraction v).2.2,
    Nat.cast_zero,Nat.cast_one,sub_zero,energyValue,residualValue,normalization]
  simp only [headerBits,List.append_assoc]

#print axioms bits_physical
end Maxwell.Continuum.StoredHeader
