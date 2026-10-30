import Maxwell.Continuum.RationalDataflowParts
import Maxwell.Continuum.CalibrationSharedDenominator

/-! Shared denominators formed directly from runtime raw rational channels.
No gcd or canonical rational representation is computed here. -/
namespace Maxwell.Continuum.RationalDataflow.SharedTable
open Maxwell.Cost
open scoped BigOperators
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι]

def denominator (a : ι→Parts) : ℕ := ∏ i, (a i).denominator

theorem denominator_pos (a : ι→Parts) (ha : ∀ i, (a i).Valid) : 0<denominator a :=
  Finset.prod_pos (fun i _ => ha i)

theorem denominator_dvd (a : ι→Parts) (i : ι) : (a i).denominator∣denominator a :=
  Finset.dvd_prod_of_mem (fun j => (a j).denominator) (Finset.mem_univ i)

def integerParts (a : ι→Parts) (i : ι) : Parts :=
  ⟨(a i).positive*(denominator a/(a i).denominator),
   (a i).negative*(denominator a/(a i).denominator),1⟩

def integerValue (a : ι→Parts) (i : ι) : ℤ :=
  (integerParts a i).positive-(integerParts a i).negative

theorem integerParts_valid (a : ι→Parts) (i : ι) : (integerParts a i).Valid := by
  exact Nat.zero_lt_one

theorem integerParts_value (a : ι→Parts) (i : ι) :
    (integerParts a i).value=(integerValue a i : ℚ) := by
  simp only [Parts.value,integerValue,integerParts,Nat.cast_one,div_one,
    Int.cast_sub,Int.cast_natCast]

theorem integerValue_sound (a : ι→Parts) (ha : ∀ i, (a i).Valid) (i : ι) :
    (integerValue a i : ℚ)/(denominator a : ℚ)=(a i).value := by
  have hd : (denominator a : ℚ)≠0 := by exact_mod_cast (denominator_pos a ha).ne'
  have hx : ((a i).denominator : ℚ)≠0 := by exact_mod_cast (ha i).ne'
  have hq : ((denominator a/(a i).denominator : ℕ):ℚ)*(a i).denominator=denominator a := by
    exact_mod_cast Nat.div_mul_cancel (denominator_dvd a i)
  rw [← integerParts_value]
  unfold integerParts Parts.value
  simp only [Nat.cast_one,div_one,Nat.cast_mul]
  apply (div_eq_div_iff hd hx).mpr
  calc
    _ = ((a i).positive-(a i).negative:ℚ)*
        (((denominator a/(a i).denominator:ℕ):ℚ)*(a i).denominator) := by ring
    _ = _ := by rw [hq]

theorem bits_power_bound (x W : ℕ) (hx : x.bits.length≤W) : x≤2^W := by
  rw [Nat.size_eq_bits_len] at hx
  exact (Nat.lt_size_self x).le.trans (Nat.pow_le_pow_right (by decide) hx)

theorem denominator_bound (a : ι→Parts) (W : ℕ) (ha : ∀ i, (a i).Width W) :
    denominator a≤2^(Fintype.card ι*W) := by
  calc
    _ ≤ ∏ _i : ι, 2^W := Finset.prod_le_prod (fun i _ => bits_power_bound _ W (ha i).2.2)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,←pow_mul]; rw [Nat.mul_comm]

theorem denominator_width (a : ι→Parts) (W : ℕ) (ha : ∀ i, (a i).Width W) :
    (denominator a).bits.length≤Fintype.card ι*W+1 := by
  rw [Nat.size_eq_bits_len]
  exact (Nat.size_le_size (denominator_bound a W ha)).trans (by simp only [Nat.size_pow]; exact le_rfl)

theorem integerParts_width (a : ι→Parts) (W : ℕ) (ha : ∀ i, (a i).Width W) (i : ι) :
    (integerParts a i).Width ((Fintype.card ι+1)*W+1) := by
  have hq : (denominator a/(a i).denominator).bits.length≤Fintype.card ι*W+1 := by
    have h := Nat.size_le_size (Nat.div_le_self (denominator a) (a i).denominator)
    rw [Nat.size_eq_bits_len]
    exact h.trans (by simpa only [Nat.size_eq_bits_len] using denominator_width a W ha)
  have hp := (RationalAccumulator.bits_mul_le _ _).trans (Nat.add_le_add (ha i).1 hq)
  have hn := (RationalAccumulator.bits_mul_le _ _).trans (Nat.add_le_add (ha i).2.1 hq)
  refine ⟨?_,?_,?_⟩
  · change ((a i).positive*(denominator a/(a i).denominator)).bits.length≤_
    nlinarith only [hp]
  · change ((a i).negative*(denominator a/(a i).denominator)).bits.length≤_
    nlinarith only [hn]
  · change (1:ℕ).bits.length≤_
    norm_num

#print axioms integerValue_sound
#print axioms integerParts_width
end Maxwell.Continuum.RationalDataflow.SharedTable
