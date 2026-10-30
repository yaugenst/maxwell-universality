import Maxwell.Continuum.ContinuumRecordEncoding
import Maxwell.Continuum.ContinuumNormalizationWords
import Maxwell.Continuum.ContinuumDetuningWords
import Maxwell.Continuum.ContinuumParameterWords

/-! A literal Boolean description of the computed continuum instance, including
every ambient unit cube, every well and test polynomial, the source records,
and the original-coordinate readout map. This file bounds representation size;
the execution theorem additionally charges how these records are generated. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition FiniteAuxiliary
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures

def headerNatCoefficient (p : Source.Parameters) : ℕ :=
  analysisBits p+outputBitCoefficient p+3

def headerBitCoefficient (p : Source.Parameters) : ℕ :=
  8*(2*headerNatCoefficient p+1)+(2*energyWordCoefficient p+1)+
    (2*analysisBits p+9)+(4*normalizationWordCoefficient p+3)+(4*detuningBitCoefficient p+1)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def headerNats : List ℕ :=
  [S.n,S.nnz,Parameters.sourcePhysicalLengths p S hm 0,
    Parameters.sourcePhysicalLengths p S hm 1,Parameters.sourcePhysicalLengths p S hm 2,
    sourcePrecision p S,momentPrecision p S,
    messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+3]

def headerBits (j : Fin (drawCount p S hm)) : List Bool :=
  (headerNats p S hm).flatMap Maxwell.Codec.nat++Maxwell.Codec.rat (energy p S hm)++
    Maxwell.Codec.rat (residual p S hm)++Maxwell.Codec.rat (normalizationScale S)++
    detuningBits p S hm j

private theorem unsigned_le_self (n : ℕ) : Maxwell.unsignedBitLength n≤n := by
  rw [Maxwell.Codec.unsignedBitLength_eq_size]
  exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))

theorem headerNats_words (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    ∀q∈headerNats p S hm,Maxwell.unsignedBitLength q≤headerNatCoefficient p*logSize S := by
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  have hmB := Maxwell.Codec.unsignedBitLength_mono (Parameters.input_le_binary S.nnz)
  rw [Maxwell.Dyadic.denominator_bitLength] at hmB
  change Maxwell.unsignedBitLength S.nnz≤logSize S+1 at hmB
  have hm' : Maxwell.unsignedBitLength S.nnz≤headerNatCoefficient p*logSize S := by
    unfold headerNatCoefficient
    nlinarith only [hmB,hℓ,Nat.zero_le (analysisBits p),Nat.zero_le (outputBitCoefficient p)]
  have hn' := (Maxwell.Codec.unsignedBitLength_mono (Source.dimension_le_nnz S hu)).trans hm'
  have hside (k : Fin 3) : Maxwell.unsignedBitLength (Parameters.sourcePhysicalLengths p S hm k)≤
      headerNatCoefficient p*logSize S :=
    (physical_side_word_bits p S hm hm2 hu k).trans (Nat.mul_le_mul_right _ (by
      unfold headerNatCoefficient
      omega))
  have hs := selected_precisions_linear p S hm hm2 hu
  have hp (q : ℕ) (hq : q≤outputBitCoefficient p*logSize S) :
      Maxwell.unsignedBitLength q≤headerNatCoefficient p*logSize S :=
    (unsigned_le_self q).trans (hq.trans (Nat.mul_le_mul_right _ (by
      unfold headerNatCoefficient
      omega)))
  intro q hq
  simp only [headerNats,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hn'
  · exact hm'
  · exact hside 0
  · exact hside 1
  · exact hside 2
  · exact hp _ hs.2.2.2.1
  · exact hp _ hs.2.2.2.2.1
  · exact hp _ hs.2.2.2.2.2.2.2

private theorem rational_serial_linear {q : ℚ} {C ℓ : ℕ}
    (hℓ : 0<ℓ) (hq : Maxwell.rationalBitLength q≤C*ℓ) :
    (Maxwell.Codec.rat q).length≤(2*C+1)*ℓ := by
  rw [Maxwell.Codec.rat_length]
  change 2*Maxwell.rationalBitLength q+1≤_
  nlinarith only [hℓ,hq]

theorem headerBits_length (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (j : Fin (drawCount p S hm)) :
    (headerBits p S hm j).length≤headerBitCoefficient p*logSize S := by
  have hℓ := Parameters.inputLog_pos S.nnz
  have hn := Maxwell.Codec.flatMap_length_le Maxwell.Codec.nat (headerNats p S hm)
    ((2*headerNatCoefficient p+1)*logSize S) (fun q hq => by
      have hq' := headerNats_words p S hm hm2 hp.1 q hq
      rw [Maxwell.Codec.nat_length]
      nlinarith only [hq',hℓ])
  change ((headerNats p S hm).flatMap Maxwell.Codec.nat).length≤
    8*((2*headerNatCoefficient p+1)*logSize S) at hn
  have he := rational_serial_linear hℓ (energy_word_bits p S hm hm2 hp.1)
  have hd := rational_serial_linear hℓ (residual_word_bits p S hm hm2 hp.1)
  have hs := rational_serial_linear hℓ (normalizationScale_word_bits p S hm hp)
  have hj := detuningBits_length p S hm hm2 hp.1 j
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hn he) hd) hs) hj
  have hc : 8*((2*headerNatCoefficient p+1)*logSize S)+
      (2*energyWordCoefficient p+1)*logSize S+(2*(analysisBits p+4)+1)*logSize S+
      (2*(2*normalizationWordCoefficient p+1)+1)*logSize S+
      (4*detuningBitCoefficient p+1)*logSize S=headerBitCoefficient p*logSize S := by
    unfold headerBitCoefficient
    ring
  simpa only [headerBits,List.length_append,Nat.add_assoc] using hsum.trans_eq hc

def readoutPlacementBits (i : Fin S.n) : List Bool :=
  placementBits p S hm (Sum.inl (SourceRouting.inputCoordinate S (precision p S hm) i))

def readoutPlacementStream : List Bool :=
  Maxwell.Codec.list (readoutPlacementBits p S hm) (List.finRange S.n)

theorem readoutPlacementStream_length (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (readoutPlacementStream p S hm).length≤
      (S.n+1)*(8*analysisBits p+20)*logSize S := by
  have hℓ := Parameters.inputLog_pos S.nnz
  have hf : ∀i∈List.finRange S.n,(readoutPlacementBits p S hm i).length≤
      (8*analysisBits p+17)*logSize S :=
    fun i _ => placementBits_length p S hm hm2 hu _
  have hl := Maxwell.Codec.list_length_le (readoutPlacementBits p S hm) (List.finRange S.n)
    ((8*analysisBits p+17)*logSize S) hf
  rw [List.length_finRange] at hl
  change (readoutPlacementStream p S hm).length≤_ at hl
  nlinarith only [hl,unsigned_le_self S.n,hℓ,Nat.zero_le (analysisBits p)]

theorem dimension_le_sites : S.n≤sites p S hm := by
  simpa only [Fintype.card_fin,sites] using
    Fintype.card_le_of_injective (sourceInputSite S (precision p S hm))
      (sourceInputSite_injective S (precision p S hm))

def recordStreamCoefficient (p : Source.Parameters) : ℝ :=
  (Parameters.sourceRecordCoefficient p+1)*(recordBitCoefficient p+3)

theorem sites_plus_one_polynomial (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (sites p S hm : ℝ)+1≤(Parameters.sourceRecordCoefficient p+1)*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^2 := by
  have hj := Parameters.source_well_record_count p S hm hm2 hu
  rw [input_sites p S hm] at hj
  have hℓ : (1 : ℝ)≤logSize S := by exact_mod_cast Parameters.inputLog_pos S.nnz
  have hpow : (logSize S : ℝ)^(3/2 : ℝ)≤(logSize S : ℝ)^2 := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hℓ (by norm_num : (3/2 : ℝ)≤(2 : ℕ)))
  have hj' : (sites p S hm : ℝ)≤Parameters.sourceRecordCoefficient p*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^2 := hj.trans (by
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg
      (Parameters.sourceRecordCoefficient_nonneg p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  have hmp : (1 : ℝ)≤(S.nnz : ℝ)^(3/2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
  have hprod := one_le_mul_of_one_le_of_one_le hmp (one_le_pow₀ hℓ (n := 2))
  nlinarith only [hj',hprod]

private theorem stream_polynomial {n C ℓ : ℕ} {A x : ℝ}
    (hn : (n : ℝ)+1≤A*x*(ℓ : ℝ)^2) (hs : (C : ℝ)≤recordBitCoefficient p+3)
    {b : ℕ} (hb : b≤(n+1)*C*ℓ^25) :
    (b : ℝ)≤A*(recordBitCoefficient p+3)*x*(ℓ : ℝ)^27 := by
  have hb' : (b : ℝ)≤((n : ℝ)+1)*C*(ℓ : ℝ)^25 := by exact_mod_cast hb
  have hnonneg : 0≤A*x*(ℓ : ℝ)^2 := (by positivity : (0 : ℝ)≤(n : ℝ)+1).trans hn
  calc
    _≤(A*x*(ℓ : ℝ)^2)*(recordBitCoefficient p+3)*(ℓ : ℝ)^25 :=
      hb'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul hn hs (Nat.cast_nonneg _) hnonneg)
        (by positivity))
    _=_ := by ring

theorem recordStreams_polynomial (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0) :
    ((wellStream p S hm).length : ℝ)≤recordStreamCoefficient p*(S.nnz : ℝ)^(3/2 : ℝ)*
      (logSize S : ℝ)^27 ∧
    ((sourceStream p S hm).length : ℝ)≤recordStreamCoefficient p*(S.nnz : ℝ)^(3/2 : ℝ)*
      (logSize S : ℝ)^27 ∧
    ((readoutPlacementStream p S hm).length : ℝ)≤recordStreamCoefficient p*(S.nnz : ℝ)^(3/2 : ℝ)*
      (logSize S : ℝ)^27 := by
  have hj := sites_plus_one_polynomial p S hm hm2 hp.1
  have hn : (S.n : ℝ)+1≤(Parameters.sourceRecordCoefficient p+1)*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^2 := by
    have hdim : (S.n : ℝ)+1≤(sites p S hm : ℝ)+1 := by
      exact_mod_cast Nat.add_le_add_right (dimension_le_sites p S hm) 1
    exact hdim.trans hj
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  have hl25 : logSize S≤(logSize S)^25 := le_self_pow₀ (by omega) (by decide : (25 : ℕ)≠0)
  have hr := (readoutPlacementStream_length p S hm hm2 hp.1).trans
    (Nat.mul_le_mul_left ((S.n+1)*(8*analysisBits p+20)) hl25)
  refine ⟨?_,?_,?_⟩
  · have h := stream_polynomial p hj
      (by simp only [Nat.cast_add,Nat.cast_ofNat]; exact le_rfl)
      (wellStream_length p S hm hm2 hp.1 hb)
    simpa only [recordStreamCoefficient,Nat.cast_add,Nat.cast_ofNat] using h
  · have h := stream_polynomial p hn
      (by simp only [Nat.cast_add,Nat.cast_ofNat]; exact le_rfl)
      (sourceStream_length p S hm hm2 hp.1 hb)
    simpa only [recordStreamCoefficient,Nat.cast_add,Nat.cast_ofNat] using h
  · have hc : (8*analysisBits p+20 : ℕ)≤recordBitCoefficient p+3 := by
      unfold recordBitCoefficient
      omega
    have h := stream_polynomial p hn (by exact_mod_cast hc) hr
    simpa only [recordStreamCoefficient,Nat.cast_add,Nat.cast_ofNat] using h

def descriptionBits (j : Fin (drawCount p S hm)) : List Bool :=
  headerBits p S hm j++ambientBits p S hm++wellStream p S hm++
    sourceStream p S hm++readoutPlacementStream p S hm

def descriptionBitCoefficient (p : Source.Parameters) : ℝ :=
  headerBitCoefficient p+ambientBitCoefficient p+3*recordStreamCoefficient p

theorem descriptionBits_polynomial (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm)) :
    ((descriptionBits p S hm j).length : ℝ)≤descriptionBitCoefficient p*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^64 := by
  have hℓ : (1 : ℝ)≤logSize S := by exact_mod_cast Parameters.inputLog_pos S.nnz
  have hm1 : (1 : ℝ)≤(S.nnz : ℝ)^(3/2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
  have hl1 : (logSize S : ℝ)≤(logSize S : ℝ)^64 := le_self_pow₀ hℓ (by decide)
  have hl25 : (logSize S : ℝ)^25≤(logSize S : ℝ)^64 := pow_le_pow_right₀ hℓ (by decide)
  have hl27 : (logSize S : ℝ)^27≤(logSize S : ℝ)^64 := pow_le_pow_right₀ hℓ (by decide)
  have hh : ((headerBits p S hm j).length : ℝ)≤(headerBitCoefficient p : ℝ)*(logSize S : ℝ) := by
    exact_mod_cast headerBits_length p S hm hm2 hp j
  have hh' : ((headerBits p S hm j).length : ℝ)≤(headerBitCoefficient p : ℝ)*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^64 := hh.trans (by gcongr; exact le_mul_of_one_le_right (by positivity) hm1)
  have ha := ambientBits_polynomial p S hm hm2 hp.1
  have hapos : 0≤ambientBitCoefficient p := by
    unfold ambientBitCoefficient Parameters.sourceVolumeCoefficient
    have := Parameters.routingVolumeCoefficient_nonneg p
    positivity
  have ha' := ha.trans (mul_le_mul_of_nonneg_left hl25
    (mul_nonneg hapos (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  have hrs := recordStreams_polynomial p S hm hm2 hp hb
  have hrpos : 0≤recordStreamCoefficient p := by
    unfold recordStreamCoefficient
    have := Parameters.sourceRecordCoefficient_nonneg p
    positivity
  have hup := mul_le_mul_of_nonneg_left hl27
    (mul_nonneg hrpos (Real.rpow_nonneg (Nat.cast_nonneg S.nnz) (3/2 : ℝ)))
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add hh' ha')
    (hrs.1.trans hup)) (hrs.2.1.trans hup)) (hrs.2.2.trans hup)
  simp only [descriptionBits,List.length_append,Nat.cast_add]
  convert hsum using 1
  unfold descriptionBitCoefficient
  ring

#print axioms headerBits_length
#print axioms recordStreams_polynomial
#print axioms descriptionBits_polynomial

end Maxwell.Continuum.RealizationParameters
