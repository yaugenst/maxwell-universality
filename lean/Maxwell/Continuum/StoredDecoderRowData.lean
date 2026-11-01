import Maxwell.Continuum.StoredDecoderRowEmission
import Maxwell.Continuum.StoredReadoutIdentity

/-! The executed row arithmetic uses the actual positive readout strength
and the affine coordinate from the produced packed-geometry record. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration Maxwell.Logical
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision FiniteAuxiliary.messageRangeBits

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
variable {saved} (geometry : Represents S (precision p S hm) saved)

include geometry in
theorem readout_numerator_pos (hb : S.source≠0) (i : Fin S.n) :
    0<wellNumerators p S hm ((sourceCircuit S (precision p S hm)).size+i.val):=by
  have positive:=(computedEnclosures p S hm).wellStrength_spec hb (readoutSite p S hm i) |>.1
  rw [readout_numerator p S hm geometry i] at positive
  have powPositive : (0:ℚ)<2^wellStoredPrecision p S hm:=by positivity
  have hp:=mul_pos positive powPositive
  rw [div_mul_cancel₀ _ (ne_of_gt powPositive)] at hp
  exact_mod_cast hp

include geometry in
theorem decoder_row_bits (hb : S.source≠0) (i : Fin S.n) (v : ℕ→ℕ)
    (coordinates : ∀j:Fin 3,(DecoderRow.coordinate v j:ℤ)=
      integerCenter p S hm (readoutSite p S hm i) j)
    (side1 : v 4705=gridSide p S hm 1) (side2 : v 4706=gridSide p S hm 2)
    (numerator : v 1000=(wellNumerators p S hm
      ((sourceCircuit S (precision p S hm)).size+i.val)).toNat)
    (power : v 144=2^wellStoredPrecision p S hm)
    (normalization : (v 4707:ℚ)/(v 4708)=normalizationScale S):
    DecoderRow.bits v=Codec.rat 0++Codec.nat 1++
      Codec.nat (gridAddress p S hm (readoutSite p S hm i)).val++
      Codec.rat (normalizationScale S*(computedEnclosures p S hm).wellStrength (readoutSite p S hm i)):=by
  have atAddress : DecoderRow.address v=(gridAddress p S hm (readoutSite p S hm i)).val:=by
    rw [gridAddress_value]
    have coordinateNat (j : Fin 3):DecoderRow.coordinate v j=
        (integerCenter p S hm (readoutSite p S hm i) j).toNat:=by
      rw [←coordinates j,Int.toNat_natCast]
    simp only [DecoderRow.address,coordinateNat,side1,side2]
  have zpos:=(readout_numerator_pos p S hm geometry hb i).le
  have zcast : ((wellNumerators p S hm
      ((sourceCircuit S (precision p S hm)).size+i.val)).toNat:ℚ)=
      (wellNumerators p S hm ((sourceCircuit S (precision p S hm)).size+i.val):ℚ):=by
    exact_mod_cast Int.toNat_of_nonneg zpos
  have weight : RationalCanonical.value false (v 1000*v 4707) (v 144*v 4708)=
      normalizationScale S*(computedEnclosures p S hm).wellStrength (readoutSite p S hm i):=by
    rw [readout_numerator p S hm geometry i,←normalization]
    simp only [RationalCanonical.value,Bool.false_eq_true,ite_false,numerator,power,
      Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,zcast]
    ring
  simp only [DecoderRow.bits,DecoderRow.rowPrefix,atAddress,weight,List.append_assoc]

#print axioms decoder_row_bits
end Maxwell.Continuum.RealizationParameters
