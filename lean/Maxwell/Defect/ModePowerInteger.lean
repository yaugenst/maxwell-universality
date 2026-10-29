import Maxwell.Defect.PowerRefinement
import Maxwell.Green.CalibrationInteger

/-! The rational mode power loop has a division-free implementation using
the same two-channel integer matrix-vector kernel as inverse calibration.
Unreduced machine words and denominators have linear growth in the degree. -/
namespace Maxwell.Defect
open Cost.CalibrationMatrix FiniteStencil
open scoped BigOperators
variable {n : ℕ}

def channelPower (A : ChannelMatrix n) (source : Channels n) : ℕ → Channels n
  | 0 => source
  | N + 1 => matvec A (channelPower A source N)

theorem channelPower_scaled (A : ChannelMatrix n) (source : Channels n)
    (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) (D V : ℕ)
    (hA : ∀ i j, (A.value i j : ℚ) = (D : ℚ) * T i j)
    (hv : ∀ i, (source.value i : ℚ) = (V : ℚ) * v i) (N : ℕ) (i : Fin n) :
    ((channelPower A source N).value i : ℚ) =
      ((V : ℚ) * (D : ℚ)^N) * rationalPowerAction T N v i := by
  induction N generalizing i with
  | zero => simpa only [channelPower, rationalPowerAction, pow_zero, mul_one] using hv i
  | succ N ih =>
    have hh := channelMatvec_scaled A (channelPower A source N) T
      (rationalPowerAction T N v) (D : ℚ) ((V : ℚ) * (D : ℚ)^N) hA
      ih i
    simpa only [channelPower, rationalPowerAction, pow_succ, mul_assoc, mul_left_comm,
      mul_comm] using hh

theorem integerPower_eq (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (D V : ℕ) (hD : 0 < D) (hV : 0 < V)
    (hT : ∀ i j, (T i j).den ∣ D) (hv : ∀ i, (v i).den ∣ V) (N : ℕ) (i : Fin n) :
    ((channelPower (integerMatrix T D) (integerSource v V) N).value i : ℚ) /
      ((V : ℚ) * (D : ℚ)^N) = rationalPowerAction T N v i := by
  rw [channelPower_scaled _ _ T v D V (integerMatrix_scaled T D hT)
    (integerSource_scaled v V hv)]
  have hden : (V : ℚ) * (D : ℚ)^N ≠ 0 := by positivity
  exact mul_div_cancel_left₀ _ hden

theorem channelPower_bound (A : ChannelMatrix n) (source : Channels n) (a b : ℕ)
    (hA : A.Bounded a) (hv : source.Bounded b) (N : ℕ) :
    (channelPower A source N).Bounded (b * (2 * n * a)^N) := by
  induction N with
  | zero => simpa only [channelPower, pow_zero, mul_one] using hv
  | succ N ih =>
    have hh := matvec_bound hA ih
    simpa only [channelPower, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hh

theorem channelPower_bit_bound (A : ChannelMatrix n) (source : Channels n) (a b : ℕ)
    (hA : A.Bounded a) (hv : source.Bounded b) (N : ℕ) (i : Fin n) :
    ((channelPower A source N).positive i).size ≤ b.size + (2*n*a).size*N ∧
    ((channelPower A source N).negative i).size ≤ b.size + (2*n*a).size*N :=
  (channelPower_bound A source a b hA hv N).bit_bound i

theorem channelPower_denominator_bit_bound (D V N : ℕ) :
    (V * D^N).size ≤ V.size + D.size*N := size_mul_pow_bound V D N

/-- The matrix-vector iteration count is exactly the power degree. -/
theorem channelPower_eq_iterate (A : ChannelMatrix n) (source : Channels n) (N : ℕ) :
    channelPower A source N = (matvec A)^[N] source := by
  induction N with
  | zero => rfl
  | succ N ih => rw [channelPower, ih, Function.iterate_succ_apply']

def modeMatrixDenominator (T : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  ∏ i, ∏ j, (T i j).den

def modeVectorDenominator (v : Fin n → ℚ) : ℕ := ∏ i, (v i).den

theorem modeMatrixDenominator_pos (T : Matrix (Fin n) (Fin n) ℚ) :
    0 < modeMatrixDenominator T :=
  Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (T i j).den_pos

theorem modeVectorDenominator_pos (v : Fin n → ℚ) : 0 < modeVectorDenominator v :=
  Finset.prod_pos fun i _ => (v i).den_pos

theorem modeMatrixDenominator_dvd (T : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (T i j).den ∣ modeMatrixDenominator T :=
  (Finset.dvd_prod_of_mem (fun j => (T i j).den) (Finset.mem_univ j)).trans
    (Finset.dvd_prod_of_mem (fun i => ∏ j, (T i j).den) (Finset.mem_univ i))

theorem modeVectorDenominator_dvd (v : Fin n → ℚ) (i : Fin n) :
    (v i).den ∣ modeVectorDenominator v :=
  Finset.dvd_prod_of_mem (fun i => (v i).den) (Finset.mem_univ i)

/-- Canonical integer implementation of any finite rational power action. -/
def rationalPowerViaChannels (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (N : ℕ) (i : Fin n) : ℚ :=
  ((channelPower (integerMatrix T (modeMatrixDenominator T))
    (integerSource v (modeVectorDenominator v)) N).value i : ℚ) /
    ((modeVectorDenominator v : ℚ) * (modeMatrixDenominator T : ℚ)^N)

theorem rationalPowerViaChannels_eq (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (N : ℕ) : rationalPowerViaChannels T v N = rationalPowerAction T N v := by
  funext i
  exact integerPower_eq T v _ _ (modeMatrixDenominator_pos T) (modeVectorDenominator_pos v)
    (modeMatrixDenominator_dvd T) (modeVectorDenominator_dvd v) N i

private theorem prod_le_pow_sum_size {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ∏ i ∈ s, f i ≤ 2 ^ ∑ i ∈ s, (f i).size := by
  calc
    _ ≤ ∏ i ∈ s, 2 ^ (f i).size := Finset.prod_le_prod (fun i _ => (Nat.lt_size_self (f i)).le)
    _ = _ := Finset.prod_pow_eq_pow_sum s (fun i => (f i).size) 2

theorem modeVectorDenominator_bit_bound (v : Fin n → ℚ) :
    (modeVectorDenominator v).size ≤ (∑ i, (v i).den.size) + 1 := by
  have hh := Nat.size_le_size (prod_le_pow_sum_size Finset.univ (fun i => (v i).den))
  simpa only [modeVectorDenominator, Nat.size_pow] using hh

theorem modeMatrixDenominator_bit_bound (T : Matrix (Fin n) (Fin n) ℚ) :
    (modeMatrixDenominator T).size ≤ (∑ i, ∑ j, (T i j).den.size) + 1 := by
  have hden : modeMatrixDenominator T ≤ 2 ^ (∑ i, ∑ j, (T i j).den.size) := by
    calc
      _ ≤ ∏ i, 2 ^ (∑ j, (T i j).den.size) :=
        Finset.prod_le_prod (fun i _ => prod_le_pow_sum_size Finset.univ (fun j => (T i j).den))
      _ = _ := Finset.prod_pow_eq_pow_sum Finset.univ (fun i => ∑ j, (T i j).den.size) 2
  have hh := Nat.size_le_size hden
  simpa only [Nat.size_pow] using hh

private theorem commonNumerator_abs_le (D A : ℕ) (q : ℚ)
    (hden : q.den ∣ D) (hq : |q| ≤ (A : ℚ)) :
    |commonNumerator D q| ≤ (D * A : ℕ) := by
  have hh : |(commonNumerator D q : ℚ)| ≤ ((D * A : ℕ) : ℚ) := by
    rw [commonNumerator_scaled D q hden, abs_mul, abs_of_nonneg (Nat.cast_nonneg D), Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg D)
  exact_mod_cast hh

theorem integerMatrix_channel_bound (T : Matrix (Fin n) (Fin n) ℚ) (D A : ℕ)
    (hden : ∀ i j, (T i j).den ∣ D) (hT : ∀ i j, |T i j| ≤ (A : ℚ)) :
    (integerMatrix T D).Bounded (D * A) := by
  intro i j
  have hh := commonNumerator_abs_le D A (T i j) (hden i j) (hT i j)
  have hpos := (le_abs_self (commonNumerator D (T i j))).trans hh
  have hneg := (neg_le_abs (commonNumerator D (T i j))).trans hh
  change (commonNumerator D (T i j)).toNat ≤ D * A ∧
    (-commonNumerator D (T i j)).toNat ≤ D * A
  constructor <;> omega

theorem integerSource_channel_bound (v : Fin n → ℚ) (V B : ℕ)
    (hden : ∀ i, (v i).den ∣ V) (hv : ∀ i, |v i| ≤ (B : ℚ)) :
    (integerSource v V).Bounded (V * B) := by
  intro i
  have hh := commonNumerator_abs_le V B (v i) (hden i) (hv i)
  have hpos := (le_abs_self (commonNumerator V (v i))).trans hh
  have hneg := (neg_le_abs (commonNumerator V (v i))).trans hh
  change (commonNumerator V (v i)).toNat ≤ V * B ∧
    (-commonNumerator V (v i)).toNat ≤ V * B
  constructor <;> omega

theorem integerPower_bit_bound (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (D V A B N : ℕ) (hT : ∀ i j, (T i j).den ∣ D) (hv : ∀ i, (v i).den ∣ V)
    (hA : ∀ i j, |T i j| ≤ (A : ℚ)) (hB : ∀ i, |v i| ≤ (B : ℚ)) (i : Fin n) :
    ((channelPower (integerMatrix T D) (integerSource v V) N).positive i).size ≤
      (V*B).size + (2*n*(D*A)).size*N ∧
    ((channelPower (integerMatrix T D) (integerSource v V) N).negative i).size ≤
      (V*B).size + (2*n*(D*A)).size*N :=
  channelPower_bit_bound _ _ _ _ (integerMatrix_channel_bound T D A hT hA)
    (integerSource_channel_bound v V B hv hB) N i

end Maxwell.Defect
