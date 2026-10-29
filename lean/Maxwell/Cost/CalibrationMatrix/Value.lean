import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Maxwell.Cost.CalibrationMatrix

open scoped BigOperators

/-- Signed values are stored as two nonnegative channels. Cancellation is
semantic: the machine never needs an integer comparison to accumulate them. -/
structure Channels (n : ℕ) where
  positive : Fin n → ℕ
  negative : Fin n → ℕ

structure ChannelMatrix (n : ℕ) where
  positive : Matrix (Fin n) (Fin n) ℕ
  negative : Matrix (Fin n) (Fin n) ℕ

def Channels.value {n : ℕ} (x : Channels n) : Fin n → ℤ :=
  fun i => (x.positive i : ℤ) - x.negative i

def ChannelMatrix.value {n : ℕ} (A : ChannelMatrix n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (A.positive i j : ℤ) - A.negative i j

def Channels.add {n : ℕ} (x y : Channels n) : Channels n :=
  ⟨fun i => x.positive i + y.positive i, fun i => x.negative i + y.negative i⟩

def Channels.scale {n : ℕ} (a : ℕ) (x : Channels n) : Channels n :=
  ⟨fun i => a*x.positive i, fun i => a*x.negative i⟩

def Channels.negate {n : ℕ} (x : Channels n) : Channels n := ⟨x.negative, x.positive⟩

def matvec {n : ℕ} (A : ChannelMatrix n) (x : Channels n) : Channels n :=
  ⟨fun i => ∑ j, (A.positive i j*x.positive j + A.negative i j*x.negative j),
   fun i => ∑ j, (A.positive i j*x.negative j + A.negative i j*x.positive j)⟩

@[simp] theorem value_add {n : ℕ} (x y : Channels n) (i : Fin n) :
    (x.add y).value i = x.value i + y.value i := by
  simp [Channels.add, Channels.value]; ring

@[simp] theorem value_scale {n : ℕ} (a : ℕ) (x : Channels n) (i : Fin n) :
    (x.scale a).value i = (a : ℤ)*x.value i := by
  simp [Channels.scale, Channels.value]; ring

@[simp] theorem value_negate {n : ℕ} (x : Channels n) (i : Fin n) :
    x.negate.value i = -x.value i := by simp [Channels.negate, Channels.value]

theorem value_matvec {n : ℕ} (A : ChannelMatrix n) (x : Channels n) (i : Fin n) :
    (matvec A x).value i = ∑ j, A.value i j*x.value j := by
  simp only [matvec, Channels.value, ChannelMatrix.value, Nat.cast_sum, Nat.cast_add, Nat.cast_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- If `H=A/D` and `s=S/D`, this is the division-free numerator recurrence
for `v + (I-s H²)h`, together with the growing numerator of the fixed source. -/
def hornerStep {n : ℕ} (A : ChannelMatrix n) (D S : ℕ)
    (state : Channels n × Channels n) : Channels n × Channels n :=
  let w := state.1.scale (D^3)
  (w, (w.add (state.2.scale (D^3))).add ((matvec A (matvec A state.2)).scale S).negate)

def horner {n : ℕ} (A : ChannelMatrix n) (D S : ℕ) (source : Channels n) :
    ℕ → Channels n × Channels n
  | 0 => (source, source)
  | N+1 => hornerStep A D S (horner A D S source N)

def inverseNumerator {n : ℕ} (A : ChannelMatrix n) (D S : ℕ)
    (source : Channels n) (N : ℕ) : Channels n :=
  (matvec A (horner A D S source N).2).scale S

@[simp] theorem hornerStep_source_value {n : ℕ} (A : ChannelMatrix n) (D S : ℕ)
    (state : Channels n × Channels n) (i : Fin n) :
    (hornerStep A D S state).1.value i = (D : ℤ)^3*state.1.value i := by
  simp [hornerStep]

theorem hornerStep_value {n : ℕ} (A : ChannelMatrix n) (D S : ℕ)
    (state : Channels n × Channels n) (i : Fin n) :
    (hornerStep A D S state).2.value i =
      (D : ℤ)^3*state.1.value i + (D : ℤ)^3*state.2.value i -
        (S : ℤ)*∑ j, A.value i j*(∑ k, A.value j k*state.2.value k) := by
  simp only [hornerStep, value_add, value_scale, value_negate, value_matvec, Nat.cast_pow]
  ring

end Maxwell.Cost.CalibrationMatrix
