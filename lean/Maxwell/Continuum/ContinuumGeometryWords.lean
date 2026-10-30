import Maxwell.Continuum.ContinuumRealizationResources
import Maxwell.Continuum.ParameterVolume

/-! The actual integer box sides and translated well centers have short
binary words. These bounds also cover every enumerated ambient unit cube. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude MasterConstants.exponent

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def integerCenter (i : SourceDecoration.Vertex S (precision p S hm)) (k : Fin 3) : ℤ :=
  2*Parameters.sourceCell p S hm (stage p S hm) i k

theorem integerCenter_real (i : SourceDecoration.Vertex S (precision p S hm)) (k : Fin 3) :
    (integerCenter p S hm i k : ℝ)=centers p S hm i k := by
  rw [centers_eq]
  simp only [integerCenter,Int.cast_mul,Int.cast_ofNat,CellGauge.latticeShift,
    PiLp.smul_apply,Bloch.integerVector_apply,smul_eq_mul]

theorem physical_side_le_count (k : Fin 3) :
    Parameters.sourcePhysicalLengths p S hm k≤count p S hm := by
  have h := Finset.single_le_prod
    (f := fun j : Fin 3 => 1+2*Parameters.sourcePhysicalLengths p S hm j)
    (s := Finset.univ) (fun _ _ => by omega) (Finset.mem_univ k)
  change _≤2*∏ j : Fin 3, (1+2*Parameters.sourcePhysicalLengths p S hm j)
  omega

theorem count_le_inverseBound : (count p S hm : ℝ) ≤ inverseBound p S hm := by
  rw [inverseBound_eq,Detuning.inverseBudget]
  apply (le_div_iff₀ (radius_pos p S hm)).mpr
  have hm1 : (1 : ℝ)≤S.nnz := by exact_mod_cast hm
  have hr := radius_upper p S hm
  have h1 : (count p S hm : ℝ)*(radius p S hm : ℝ)≤count p S hm :=
    mul_le_of_le_one_right (by positivity) (hr.trans (by norm_num))
  have h2 : (count p S hm : ℝ)≤64*(S.nnz : ℝ)*(count p S hm : ℝ) := by
    have hN : (0 : ℝ)≤count p S hm := Nat.cast_nonneg _
    nlinarith only [hm1,hN]
  exact h1.trans h2

theorem count_binary (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    count p S hm≤2^scaleBits p S := by
  exact_mod_cast (count_le_inverseBound p S hm).trans (inverse_binary_real p S hm hm2 hu)

theorem physical_side_word_bits (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) (k : Fin 3) :
    Maxwell.unsignedBitLength (Parameters.sourcePhysicalLengths p S hm k)≤
      (analysisBits p+1)*logSize S := by
  have h := Maxwell.Codec.unsignedBitLength_mono
    ((physical_side_le_count p S hm k).trans (count_binary p S hm hm2 hu))
  rw [Maxwell.Dyadic.denominator_bitLength] at h
  have hℓ := Parameters.inputLog_pos S.nnz
  unfold scaleBits at h
  nlinarith only [h,hℓ]

theorem integerCenter_bounds (i : SourceDecoration.Vertex S (precision p S hm)) (k : Fin 3) :
    0 ≤ integerCenter p S hm i k ∧
      integerCenter p S hm i k≤(Parameters.sourcePhysicalLengths p S hm k : ℤ) := by
  have h := centers_buffered p S hm i k
  rw [← integerCenter_real p S hm i k,box_sides p S hm] at h
  have hb : (0 : ℝ)≤buffer p S hm := Nat.cast_nonneg _
  have hL : (0 : ℝ)≤length p S hm := Nat.cast_nonneg _
  have hlo : (0 : ℝ)≤(integerCenter p S hm i k : ℝ) := by
    nlinarith only [h.1,hb,hL]
  have hhi : (integerCenter p S hm i k : ℝ)≤Parameters.sourcePhysicalLengths p S hm k := by
    nlinarith only [h.2,hb,hL]
  exact ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩

theorem integerCenter_word_bits (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (i : SourceDecoration.Vertex S (precision p S hm)) (k : Fin 3) :
    Maxwell.signedBitLength (integerCenter p S hm i k)≤(analysisBits p+2)*logSize S := by
  have hi := integerCenter_bounds p S hm i k
  have habs : (integerCenter p S hm i k).natAbs≤Parameters.sourcePhysicalLengths p S hm k := by
    have ha : |integerCenter p S hm i k|≤(Parameters.sourcePhysicalLengths p S hm k : ℤ) := by
      rw [abs_of_nonneg hi.1]
      exact hi.2
    rw [← Int.natCast_natAbs] at ha
    exact_mod_cast ha
  have hb := (Maxwell.Codec.unsignedBitLength_mono habs).trans
    (physical_side_word_bits p S hm hm2 hu k)
  have hℓ := Parameters.inputLog_pos S.nnz
  unfold Maxwell.signedBitLength
  nlinarith only [hb,hℓ]

#print axioms integerCenter_real
#print axioms physical_side_word_bits
#print axioms integerCenter_word_bits

end Maxwell.Continuum.RealizationParameters
