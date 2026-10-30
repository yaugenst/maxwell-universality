import Maxwell.Continuum.CalibrationCompactFourier
import Maxwell.Continuum.RationalFiniteWidths

/-! The finite encoder computes its actual Fourier-frequency bound by
rational ceiling; no frequency-search success condition is needed. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber RationalWords

def templateFrequencyBound (M : ℕ) (L : ℚ) (R : ℕ) : ℕ :=
  ⌈|L| * (R : ℚ)/(2*(M : ℚ))⌉₊

variable (M : ℕ) [NeZero M]

theorem templateFrequencyBound_spec (L : ℚ) (R : ℕ) :
    |L| * (R : ℚ)≤2*(M : ℚ)*templateFrequencyBound M L R := by
  have hm : (0 : ℚ)<M := by exact_mod_cast NeZero.pos M
  have h := (div_le_iff₀ (by positivity : (0 : ℚ)<2*(M : ℚ))).mp
    (Nat.le_ceil (|L| * (R : ℚ)/(2*(M : ℚ))))
  simpa only [templateFrequencyBound,mul_comm] using h

theorem templateFrequencyBound_le (L : ℚ) (R Q : ℕ)
    (hQ : |L| * (R : ℚ)≤2*(M : ℚ)*Q) : templateFrequencyBound M L R≤Q := by
  have hm : (0 : ℚ)<M := by exact_mod_cast NeZero.pos M
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by positivity : (0 : ℚ)<2*(M : ℚ))).mpr
  simpa only [mul_comm] using hQ

theorem templateFrequency_computed_bound (L : ℚ) (R : ℕ) {n : Alias}
    (hn : n∈PeriodicSampling.Product.frequencyCube R) (i : Fin 3) :
    |templateFrequency M L n i|≤templateFrequencyBound M L R :=
  templateFrequency_bound M L R _ (templateFrequencyBound_spec M L R) hn i

theorem templateFrequency_width (L : ℚ) (n : Alias) (i : Fin 3) {A R : ℕ}
    (hL : Width L A) (hn : n∈PeriodicSampling.Product.frequencyCube R) :
    Width (templateFrequency M L n i) (A+R.bits.length+M.bits.length+4) := by
  have hn' : (n i).natAbs≤R := by
    have h := (PeriodicSampling.Product.mem_frequencyCube R n).mp hn i
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hw := width_int (n i)
  have hb : (n i).natAbs.bits.length≤R.bits.length := by
    simpa only [← Nat.size_eq_bits_len] using Nat.size_le_size hn'
  have hni : Width (n i : ℚ) (R.bits.length+1) := hw.mono (by omega)
  have hmi : Width (M : ℚ) (M.bits.length+1) := by
    simpa only [Int.natAbs_natCast,Int.cast_natCast] using width_int (M : ℤ)
  have htwo : Width (2 : ℚ) 2 := by constructor <;> decide
  have hm : (0 : ℚ)<M := by exact_mod_cast NeZero.pos M
  exact (((hL.mul hni).mul ((htwo.mul hmi).inv (by positivity))).mono (by omega))

#print axioms templateFrequencyBound_spec
#print axioms templateFrequency_width

end Maxwell.Continuum.Calibration.Supercell
