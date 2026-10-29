import Maxwell.Cost.CalibrationMatrix.Value
import Mathlib.Data.Nat.Size

/-! Bounds on the unreduced nonnegative channels of the exact integer
Horner implementation. These bounds cover actual stored values, including
cancellation that has not been performed by the machine. -/
namespace Maxwell.Cost.CalibrationMatrix
open scoped BigOperators
set_option maxHeartbeats 600000

/-- Both independently stored sign channels satisfy the same bound. -/
def Channels.Bounded {n : ℕ} (x : Channels n) (B : ℕ) : Prop :=
  ∀ i, x.positive i ≤ B ∧ x.negative i ≤ B

def ChannelMatrix.Bounded {n : ℕ} (A : ChannelMatrix n) (B : ℕ) : Prop :=
  ∀ i j, A.positive i j ≤ B ∧ A.negative i j ≤ B

theorem Channels.Bounded.mono {n : ℕ} {x : Channels n} {B C : ℕ}
    (hx : x.Bounded B) (hBC : B ≤ C) : x.Bounded C :=
  fun i => ⟨(hx i).1.trans hBC, (hx i).2.trans hBC⟩

theorem Channels.Bounded.add {n : ℕ} {x y : Channels n} {B C : ℕ}
    (hx : x.Bounded B) (hy : y.Bounded C) : (x.add y).Bounded (B + C) :=
  fun i => ⟨Nat.add_le_add (hx i).1 (hy i).1, Nat.add_le_add (hx i).2 (hy i).2⟩

theorem Channels.Bounded.scale {n : ℕ} {x : Channels n} {B : ℕ}
    (hx : x.Bounded B) (a : ℕ) : (x.scale a).Bounded (a * B) :=
  fun i => ⟨Nat.mul_le_mul_left a (hx i).1, Nat.mul_le_mul_left a (hx i).2⟩

theorem Channels.Bounded.negate {n : ℕ} {x : Channels n} {B : ℕ}
    (hx : x.Bounded B) : x.negate.Bounded B := fun i => ⟨(hx i).2, (hx i).1⟩

theorem matvec_bound {n : ℕ} {A : ChannelMatrix n} {x : Channels n} {a b : ℕ}
    (hA : A.Bounded a) (hx : x.Bounded b) : (matvec A x).Bounded (2 * n * a * b) := by
  intro i
  constructor
  · change (∑ j, (A.positive i j * x.positive j + A.negative i j * x.negative j)) ≤ _
    calc
      _ ≤ ∑ _j : Fin n, (a * b + a * b) := Finset.sum_le_sum fun j _ =>
        Nat.add_le_add (Nat.mul_le_mul (hA i j).1 (hx j).1)
          (Nat.mul_le_mul (hA i j).2 (hx j).2)
      _ = _ := by simp; ring
  · change (∑ j, (A.positive i j * x.negative j + A.negative i j * x.positive j)) ≤ _
    calc
      _ ≤ ∑ _j : Fin n, (a * b + a * b) := Finset.sum_le_sum fun j _ =>
        Nat.add_le_add (Nat.mul_le_mul (hA i j).1 (hx j).2)
          (Nat.mul_le_mul (hA i j).2 (hx j).1)
      _ = _ := by simp; ring

/-- One multiplication factor covers both the accumulated source and the
Horner vector, before any rational cancellation. -/
def channelGrowth (n a D S : ℕ) : ℕ := 2 * D ^ 3 + S * (2 * n * a) ^ 2

theorem hornerStep_bound {n : ℕ} {A : ChannelMatrix n} {a b : ℕ}
    (hA : A.Bounded a) (D S : ℕ) (state : Channels n × Channels n)
    (hw : state.1.Bounded b) (hx : state.2.Bounded b) :
    (hornerStep A D S state).1.Bounded (channelGrowth n a D S * b) ∧
      (hornerStep A D S state).2.Bounded (channelGrowth n a D S * b) := by
  constructor
  · exact (hw.scale (D ^ 3)).mono (Nat.mul_le_mul_right b (by unfold channelGrowth; omega))
  · have h := ((hw.scale (D ^ 3)).add (hx.scale (D ^ 3))).add
      (((matvec_bound hA (matvec_bound hA hx)).scale S).negate)
    convert h using 1
    · rfl
    · unfold channelGrowth
      ring

theorem horner_bound {n : ℕ} {A : ChannelMatrix n} {a b : ℕ}
    (hA : A.Bounded a) (D S : ℕ) (source : Channels n) (hv : source.Bounded b) (N : ℕ) :
    (horner A D S source N).1.Bounded (b * channelGrowth n a D S ^ N) ∧
      (horner A D S source N).2.Bounded (b * channelGrowth n a D S ^ N) := by
  induction N with
  | zero => simpa [horner] using And.intro hv hv
  | succ N ih =>
    have h := hornerStep_bound hA D S (horner A D S source N) ih.1 ih.2
    simpa only [horner, pow_succ, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using h

theorem inverseNumerator_bound {n : ℕ} {A : ChannelMatrix n} {a b : ℕ}
    (hA : A.Bounded a) (D S : ℕ) (source : Channels n) (hv : source.Bounded b) (N : ℕ) :
    (inverseNumerator A D S source N).Bounded
      ((S * (2 * n * a) * b) * channelGrowth n a D S ^ N) := by
  have h := (matvec_bound hA (horner_bound hA D S source hv N).2).scale S
  convert h using 1
  · rfl
  · ring

/-- Multiplication by an exponential contributes linearly many bits. -/
theorem size_mul_pow_bound (V F N : ℕ) :
    (V * F ^ N).size ≤ V.size + F.size * N := by
  apply Nat.size_le.mpr
  have hp : F ^ N ≤ (2 ^ F.size) ^ N := Nat.pow_le_pow_left (Nat.lt_size_self F).le N
  calc
    _ ≤ V * (2 ^ F.size) ^ N := Nat.mul_le_mul_left V hp
    _ < 2 ^ V.size * (2 ^ F.size) ^ N := Nat.mul_lt_mul_of_pos_right
      (Nat.lt_size_self V) (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_add]

theorem Channels.Bounded.bit_bound {n : ℕ} {x : Channels n} {V F N : ℕ}
    (hx : x.Bounded (V * F ^ N)) (i : Fin n) :
    (x.positive i).size ≤ V.size + F.size * N ∧
      (x.negative i).size ≤ V.size + F.size * N :=
  ⟨(Nat.size_le_size (hx i).1).trans (size_mul_pow_bound V F N),
   (Nat.size_le_size (hx i).2).trans (size_mul_pow_bound V F N)⟩

/-- This bound concerns the unreduced machine channels, so it remains valid
even when exponentially large positive and negative terms cancel. -/
theorem horner_bit_bound {n : ℕ} {A : ChannelMatrix n} {a b : ℕ}
    (hA : A.Bounded a) (D S : ℕ) (source : Channels n) (hv : source.Bounded b)
    (N : ℕ) (i : Fin n) :
    ((horner A D S source N).1.positive i).size ≤ b.size +
        (channelGrowth n a D S).size * N ∧
    ((horner A D S source N).1.negative i).size ≤ b.size +
        (channelGrowth n a D S).size * N ∧
    ((horner A D S source N).2.positive i).size ≤ b.size +
        (channelGrowth n a D S).size * N ∧
    ((horner A D S source N).2.negative i).size ≤ b.size +
        (channelGrowth n a D S).size * N := by
  have h := horner_bound hA D S source hv N
  exact ⟨(h.1.bit_bound i).1, (h.1.bit_bound i).2,
    (h.2.bit_bound i).1, (h.2.bit_bound i).2⟩

theorem inverseNumerator_bit_bound {n : ℕ} {A : ChannelMatrix n} {a b : ℕ}
    (hA : A.Bounded a) (D S : ℕ) (source : Channels n) (hv : source.Bounded b)
    (N : ℕ) (i : Fin n) :
    ((inverseNumerator A D S source N).positive i).size ≤
        (S * (2 * n * a) * b).size + (channelGrowth n a D S).size * N ∧
    ((inverseNumerator A D S source N).negative i).size ≤
        (S * (2 * n * a) * b).size + (channelGrowth n a D S).size * N :=
  (inverseNumerator_bound hA D S source hv N).bit_bound i

/-- The exact unreduced denominator also has linear bit length. -/
theorem inverseDenominator_bit_bound (V D N : ℕ) :
    (V * D ^ (3 * N + 2)).size ≤ V.size + D.size * (3 * N + 2) :=
  size_mul_pow_bound V D (3 * N + 2)

/-- The growth factor has logarithmic size in the matrix dimension and
coefficient bounds, despite the use of two unreduced sign channels. -/
theorem channelGrowth_le_pow (n a D S d s l b : ℕ)
    (hD : D ≤ 2 ^ d) (hS : S ≤ 2 ^ s) (hn : n ≤ 2 ^ l) (ha : a ≤ 2 ^ b) :
    channelGrowth n a D S ≤ 2 ^ (max (3 * d + 1) (s + 2 * (1 + l + b)) + 1) := by
  have hfirst : 2 * D ^ 3 ≤ 2 ^ (3 * d + 1) := by
    calc
      _ ≤ 2 * (2 ^ d) ^ 3 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hD 3)
      _ = _ := by
        rw [← pow_mul, Nat.mul_comm d 3, pow_succ]
        exact Nat.mul_comm _ _
  have hsecond : S * (2 * n * a) ^ 2 ≤ 2 ^ (s + 2 * (1 + l + b)) := by
    calc
      _ ≤ 2 ^ s * (2 * 2 ^ l * 2 ^ b) ^ 2 :=
        Nat.mul_le_mul hS (Nat.pow_le_pow_left
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) ha) 2)
      _ = _ := by
        have ht : 2 * 2 ^ l * 2 ^ b = 2 ^ (1 + l + b) := by
          rw [pow_add, pow_add, pow_one]
        rw [ht, ← pow_mul, ← pow_add]
        congr 1
        ring
  have hm₁ : 2 ^ (3 * d + 1) ≤ 2 ^ max (3 * d + 1) (s + 2 * (1 + l + b)) :=
    Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  have hm₂ : 2 ^ (s + 2 * (1 + l + b)) ≤ 2 ^ max (3 * d + 1) (s + 2 * (1 + l + b)) :=
    Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  unfold channelGrowth
  calc
    _ ≤ 2 ^ max (3 * d + 1) (s + 2 * (1 + l + b)) +
        2 ^ max (3 * d + 1) (s + 2 * (1 + l + b)) :=
      Nat.add_le_add (hfirst.trans hm₁) (hsecond.trans hm₂)
    _ = _ := by rw [pow_succ]; omega

theorem channelGrowth_size_bound (n a D S d s l b : ℕ)
    (hD : D ≤ 2 ^ d) (hS : S ≤ 2 ^ s) (hn : n ≤ 2 ^ l) (ha : a ≤ 2 ^ b) :
    (channelGrowth n a D S).size ≤ max (3 * d + 1) (s + 2 * (1 + l + b)) + 2 := by
  have h := Nat.size_le_size (channelGrowth_le_pow n a D S d s l b hD hS hn ha)
  simpa only [Nat.size_pow, Nat.add_assoc] using h

/-- Explicit bit bound in input bit lengths, dimension bits, and iteration
count. This is linear in `N` with coefficients logarithmic in dimension. -/
theorem horner_bit_bound_explicit {n : ℕ} {A : ChannelMatrix n} {a v : ℕ}
    (hA : A.Bounded a) (D S : ℕ) (source : Channels n) (hv : source.Bounded v)
    (d s l b : ℕ) (hD : D ≤ 2 ^ d) (hS : S ≤ 2 ^ s) (hn : n ≤ 2 ^ l)
    (ha : a ≤ 2 ^ b) (N : ℕ) (i : Fin n) :
    ((horner A D S source N).2.positive i).size ≤ v.size +
        (max (3 * d + 1) (s + 2 * (1 + l + b)) + 2) * N ∧
    ((horner A D S source N).2.negative i).size ≤ v.size +
        (max (3 * d + 1) (s + 2 * (1 + l + b)) + 2) * N := by
  have h := (horner_bound hA D S source hv N).2.bit_bound i
  have hb := channelGrowth_size_bound n a D S d s l b hD hS hn ha
  exact ⟨h.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_right N hb) _),
    h.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right N hb) _)⟩

end Maxwell.Cost.CalibrationMatrix
