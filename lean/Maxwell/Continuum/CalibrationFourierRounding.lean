import Maxwell.Continuum.CalibrationFiniteData
import Maxwell.Continuum.CalibrationFullSupport
import Maxwell.Continuum.CalibrationCompactFourier
import Maxwell.Continuum.ComplexDyadic
import Maxwell.Continuum.DyadicMagnitudeBits

/-! The actual dyadic serialization coefficients of a finite rational
Fourier vector, with exact represented values and global rounding error. -/

namespace Maxwell.Continuum.Calibration

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open FreeFiber PeriodicSampling

def roundFourierCoefficient (B : ℕ) (v : FourierData) (n : Alias) (j : Fin 3) : ComplexDyadic B :=
  (roundDyadic B (v.field n j).1,roundDyadic B (v.field n j).2)

def roundFourierField (B : ℕ) (v : FourierData) : RationalAliasField := fun n j =>
  ((roundFourierCoefficient B v n j).1.value,(roundFourierCoefficient B v n j).2.value)

theorem roundFourierField_supported (B : ℕ) (v : FourierData) :
    RationalSupported (roundFourierField B v) v.radius := by
  intro n hn j
  simp only [roundFourierField,roundFourierCoefficient,v.supported n hn j]
  simp [roundDyadic,Dyadic.value]

def roundFourierData (B : ℕ) (v : FourierData) : FourierData :=
  FourierData.ofSupported (roundFourierField B v) v.radius

theorem roundFourierData_radius (B : ℕ) (v : FourierData) : (roundFourierData B v).radius=v.radius := rfl

theorem roundFourierData_field (B : ℕ) (v : FourierData) :
    (roundFourierData B v).field=roundFourierField B v :=
  FourierData.ofSupported_field (roundFourierField_supported B v)

theorem roundFourierData_coordinate (B : ℕ) (v : FourierData) (n : Alias) (j : Fin 3) :
    complexDyadicValue (roundFourierCoefficient B v n j)=(roundFourierData B v).value n j := by
  rw [← (roundFourierData B v).represents,roundFourierData_field]
  rw [rationalComplexValue_eq]
  rfl

theorem roundFourierCoefficient_error (B : ℕ) (v : FourierData) (n : Alias) (j : Fin 3) :
    ‖v.value n j-complexDyadicValue (roundFourierCoefficient B v n j)‖≤2*(1/2 : ℝ)^B := by
  have hr := roundDyadic_error B (v.field n j).1
  have hi := roundDyadic_error B (v.field n j).2
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  rw [← v.represents]
  simp only [rationalComplexValue_eq,complexDyadicValue,roundFourierCoefficient,
    Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.ratCast_re,Complex.ratCast_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,sub_zero,add_zero,zero_add]
  linarith

noncomputable section

theorem finiteFiber_norm_sum {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R) :
    ‖u‖≤∑ n ∈ Product.frequencyCube R, ∑ j : Fin 3, ‖u n j‖ := by
  classical
  have hz (n : Alias) (hn : n∉Product.frequencyCube R) : u n=0 :=
    hu n (by simpa only [Product.mem_frequencyCube,not_forall,not_le] using hn)
  have hs := Supercell.sum_single_eq (Product.frequencyCube R) u hz
  have hsum := norm_sum_le (Product.frequencyCube R)
    (fun n : Alias => (lp.single (2 : ENNReal) n (u n) : FiberSpace))
  rw [hs] at hsum
  simp only [lp.norm_single (by norm_num : (0 : ENNReal)<2)] at hsum
  apply hsum.trans
  apply Finset.sum_le_sum
  intro n _
  apply (sq_le_sq₀ (norm_nonneg (u n))
    (Finset.sum_nonneg fun j _ => norm_nonneg (u n j))).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

theorem roundFourierData_error (B : ℕ) (v : FourierData) :
    ‖(roundFourierData B v).value-v.value‖≤6*((2*v.radius+1 : ℕ) : ℝ)^3*(1/2 : ℝ)^B := by
  have hv : AliasSupported v.value v.radius := representedFiber_supported _ v.supported
  have hw : AliasSupported (roundFourierData B v).value v.radius :=
    representedFiber_supported _ (roundFourierData B v).supported
  apply (finiteFiber_norm_sum (hw.sub hv)).trans
  calc
    _ ≤ ∑ _n ∈ Product.frequencyCube v.radius,∑ _j : Fin 3,2*(1/2 : ℝ)^B := by
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro j _
      change ‖(roundFourierData B v).value n j-v.value n j‖≤_
      rw [← roundFourierData_coordinate,norm_sub_rev]
      exact roundFourierCoefficient_error B v n j
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Product.frequencyCube_card,Nat.cast_pow]
      ring

theorem roundFourierCoefficient_mass (B : ℕ) (v : FourierData) :
    (∑ n ∈ Product.frequencyCube v.radius,∑ j : Fin 3,
      ‖complexDyadicValue (roundFourierCoefficient B v n j)‖)≤
      (v.mass : ℝ)+6*((2*v.radius+1 : ℕ) : ℝ)^3*(1/2 : ℝ)^B := by
  have hs : (∑ n ∈ Product.frequencyCube v.radius,∑ j : Fin 3,
      ‖complexDyadicValue (roundFourierCoefficient B v n j)‖)≤
      ∑ n ∈ Product.frequencyCube v.radius,∑ j : Fin 3,(‖v.value n j‖+2*(1/2 : ℝ)^B) := by
    apply Finset.sum_le_sum
    intro n _
    apply Finset.sum_le_sum
    intro j _
    have ht := norm_le_norm_sub_add (complexDyadicValue (roundFourierCoefficient B v n j)) (v.value n j)
    rw [norm_sub_rev] at ht
    exact ht.trans ((add_le_add (roundFourierCoefficient_error B v n j) le_rfl).trans_eq (add_comm _ _))
  apply hs.trans
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Product.frequencyCube_card,Nat.cast_pow]
  have he := v.coefficient_norm_sum
  nlinarith only [he]

theorem roundFourierCoefficient_norm (B : ℕ) (v : FourierData) (n : Alias) (j : Fin 3) :
    ‖complexDyadicValue (roundFourierCoefficient B v n j)‖≤‖v.value‖+2 := by
  have hc : ‖v.value n j‖≤‖v.value‖ :=
    (PiLp.norm_apply_le (v.value n) j).trans (lp.norm_apply_le_norm (by norm_num) v.value n)
  have hh : (1/2 : ℝ)^B≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := norm_le_norm_sub_add (complexDyadicValue (roundFourierCoefficient B v n j)) (v.value n j)
  rw [norm_sub_rev] at ht
  have he := roundFourierCoefficient_error B v n j
  linarith

theorem roundFourierCoefficient_bits (B A : ℕ) (v : FourierData) (hv : ‖v.value‖≤(2 : ℝ)^A)
    (n : Alias) (j : Fin 3) :
    (complexDyadicBits (roundFourierCoefficient B v n j)).length≤4*(B+A+4) := by
  have ha : (1 : ℝ)≤(2 : ℝ)^A := one_le_pow₀ (by norm_num)
  apply (complexDyadicBits_length (roundFourierCoefficient B v n j) (B := A+2) ?_).trans_eq
    (by omega)
  have hn := roundFourierCoefficient_norm B v n j
  rw [pow_add]
  norm_num
  linarith

#print axioms roundFourierData_error
#print axioms roundFourierCoefficient_bits

end
end Maxwell.Continuum.Calibration
