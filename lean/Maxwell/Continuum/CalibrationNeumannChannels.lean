import Maxwell.Continuum.CalibrationSharedDenominator
import Maxwell.Cost.CalibrationMatrix.Bounds
import Maxwell.Cost.CalibrationMatrix.Horner.UniformWidth

/-! Cancellation-safe integer channels for the actual shared-denominator affine recurrence. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost.CalibrationMatrix
open scoped BigOperators
set_option maxHeartbeats 2000000

def integerChannels {n : ℕ} (b : Fin n→ℤ) : Channels n :=
  ⟨fun i => (b i).toNat,fun i => (-b i).toNat⟩

def integerMatrix {n : ℕ} (A : Fin n→Fin n→ℤ) : ChannelMatrix n :=
  ⟨fun i j => (A i j).toNat,fun i j => (-A i j).toNat⟩

@[simp] theorem integerChannels_value {n : ℕ} (b : Fin n→ℤ) : (integerChannels b).value=b := by
  funext i
  exact Int.toNat_sub_toNat_neg (b i)

@[simp] theorem integerMatrix_value {n : ℕ} (A : Fin n→Fin n→ℤ) : (integerMatrix A).value=A := by
  funext i j
  exact Int.toNat_sub_toNat_neg (A i j)

def channelStep {n : ℕ} (A : ChannelMatrix n) (D : ℕ) (state : Channels n×Channels n) :
    Channels n×Channels n :=
  let w := state.1.scale D
  (w,w.add (matvec A state.2))

/-- State zero already contains the first numerator, X₁=b. -/
def channels {n : ℕ} (A : ChannelMatrix n) (D : ℕ) (b : Channels n) : ℕ→Channels n×Channels n
  | 0 => (b,b)
  | k+1 => channelStep A D (channels A D b k)

theorem channels_source_value {n : ℕ} (A : ChannelMatrix n) (D : ℕ) (b : Channels n)
    (k : ℕ) (i : Fin n) : (channels A D b k).1.value i=(D:ℤ)^k*b.value i := by
  induction k with
  | zero => simp [channels]
  | succ k ih =>
    simp only [channels,channelStep,value_scale,ih,pow_succ]
    ring

theorem channels_numerator_value {n : ℕ} (A : ChannelMatrix n) (D : ℕ) (b : Channels n)
    (k : ℕ) (i : Fin n) :
    (channels A D b k).2.value i=sharedNumerator D A.value b.value (k+1) i := by
  induction k generalizing i with
  | zero => simp [channels,sharedNumerator]
  | succ k ih =>
    simp only [channels,channelStep,value_add,value_scale,value_matvec,
      channels_source_value,ih,sharedNumerator,pow_succ]
    congr 1
    ring

theorem channels_rational_value {n : ℕ} (A : ChannelMatrix n) (D : ℕ) (hD : 0<D)
    (b : Channels n) (k : ℕ) (i : Fin n) :
    ((channels A D b k).2.value i : ℚ)/(D:ℚ)^(k+1)=
      sharedRationalIteration D A.value b.value (k+1) i := by
  rw [channels_numerator_value]
  exact sharedNumerator_sound D hD A.value b.value (k+1) i

def growth (n a D : ℕ) : ℕ := D+2*n*a

theorem channelStep_bound {n : ℕ} {A : ChannelMatrix n} {a v : ℕ}
    (hA : A.Bounded a) (D : ℕ) (state : Channels n×Channels n)
    (hw : state.1.Bounded v) (hx : state.2.Bounded v) :
    (channelStep A D state).1.Bounded (growth n a D*v) ∧
      (channelStep A D state).2.Bounded (growth n a D*v) := by
  constructor
  · exact (hw.scale D).mono (Nat.mul_le_mul_right v (by unfold growth; omega))
  · convert (hw.scale D).add (matvec_bound hA hx) using 1
    · rfl
    · unfold growth
      ring

theorem channels_bound {n : ℕ} {A : ChannelMatrix n} {a v : ℕ}
    (hA : A.Bounded a) (D : ℕ) (b : Channels n) (hb : b.Bounded v) (k : ℕ) :
    (channels A D b k).1.Bounded (v*growth n a D^k) ∧
      (channels A D b k).2.Bounded (v*growth n a D^k) := by
  induction k with
  | zero => simpa only [channels,pow_zero,Nat.mul_one] using And.intro hb hb
  | succ k ih =>
    have h := channelStep_bound hA D (channels A D b k) ih.1 ih.2
    simpa only [channels,pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

def uniformWidth (n a v D N : ℕ) : ℕ := ((growth n a D+1)*v).size+(growth n a D).size*(N+1)

theorem channels_uniform_width {n : ℕ} {A : ChannelMatrix n} {a v : ℕ}
    (hA : A.Bounded a) (D : ℕ) (b : Channels n) (hb : b.Bounded v)
    (N W : ℕ) (hW : uniformWidth n a v D N≤W) (k : ℕ) (hk : k≤N+1) :
    Horner.FitsWidth W (channels A D b k).1 ∧
      Horner.FitsWidth W (channels A D b k).2 ∧
      Horner.FitsWidth W (matvec A (channels A D b k).2) := by
  have h := channels_bound hA D b hb k
  have hv : v≤(growth n a D+1)*v := by nlinarith
  have hm : 2*n*a*v≤(growth n a D+1)*v := by unfold growth; nlinarith
  have hp := matvec_bound hA h.2
  have hp' : (matvec A (channels A D b k).2).Bounded (((growth n a D+1)*v)*growth n a D^k) := by
    apply hp.mono
    calc
      _ = (2*n*a*v)*growth n a D^k := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hm
  exact ⟨Horner.bounded_fits_width (h.1.mono (Nat.mul_le_mul_right _ hv)) hk hW,
    Horner.bounded_fits_width (h.2.mono (Nat.mul_le_mul_right _ hv)) hk hW,
    Horner.bounded_fits_width hp' hk hW⟩

#print axioms channels_rational_value
#print axioms channels_uniform_width

end Maxwell.Continuum.Calibration.NeumannMachine
