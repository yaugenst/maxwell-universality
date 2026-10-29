import Maxwell.Cost.CalibrationMatrix.Horner.Width
import Maxwell.Cost.CalibrationMatrix.Bounds

namespace Maxwell.Cost.CalibrationMatrix.Horner

/-- One common width covers every unreduced channel in the recurrence and
its terminal product. Its dependence on the iteration count is linear. -/
def uniformPrefix (n a v S : ℕ) : ℕ := (S+1)*(2*n*a+1)^2*v

def uniformWidth (n a v D S N : ℕ) : ℕ :=
  (uniformPrefix n a v S).size+(channelGrowth n a D S).size*N

theorem bounded_fits_width {n : ℕ} {x : Channels n} {V F k N W : ℕ}
    (h : x.Bounded (V*F^k)) (hk : k ≤ N) (hw : V.size+F.size*N ≤ W) : FitsWidth W x := by
  constructor
  · intro i
    rw [Nat.size_eq_bits_len]
    exact (h.bit_bound i).1.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left F.size hk) V.size).trans hw)
  · intro i
    rw [Nat.size_eq_bits_len]
    exact (h.bit_bound i).2.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left F.size hk) V.size).trans hw)

/-- The same numerical slot width bounds both live Horner channels, both
intermediate dense products, and the final inverse numerator at every step. -/
theorem uniform_width {n : ℕ} {A : ChannelMatrix n} {a v : ℕ}
    (hA : A.Bounded a) (D S : ℕ) (source : Channels n) (hv : source.Bounded v)
    (N W : ℕ) (hwidth : uniformWidth n a v D S N ≤ W) (k : ℕ) (hk : k ≤ N) :
    FitsWidth W (horner A D S source k).1 ∧
    FitsWidth W (horner A D S source k).2 ∧
    FitsWidth W (matvec A (horner A D S source k).2) ∧
    FitsWidth W (matvec A (matvec A (horner A D S source k).2)) ∧
    FitsWidth W (inverseNumerator A D S source k) := by
  let C := 2*n*a
  let M := uniformPrefix n a v S
  let F := channelGrowth n a D S
  have hc : C ≤ (C+1)^2 := by nlinarith
  have hcc : C^2 ≤ (C+1)^2 := by nlinarith
  have hbase : 1 ≤ (S+1)*(C+1)^2 := by
    have hh : 0 < (S+1)*(C+1)^2 := by positivity
    omega
  have hcoef : C ≤ (S+1)*(C+1)^2 := by
    calc
      C ≤ 1*(C+1)^2 := by simpa using hc
      _ ≤ _ := by gcongr;omega
  have hcoef2 : C^2 ≤ (S+1)*(C+1)^2 := by
    calc
      C^2 ≤ 1*(C+1)^2 := by simpa using hcc
      _ ≤ _ := by gcongr;omega
  have hscale : S*C ≤ (S+1)*(C+1)^2 := Nat.mul_le_mul (by omega) hc
  have hM0 : v ≤ M := by simpa [M,uniformPrefix,C] using Nat.mul_le_mul_right v hbase
  have hM1 : C*v ≤ M := Nat.mul_le_mul_right v hcoef
  have hM2 : C^2*v ≤ M := Nat.mul_le_mul_right v hcoef2
  have hMS : S*C*v ≤ M := Nat.mul_le_mul_right v hscale
  have hstate := horner_bound hA D S source hv k
  have hw0 : (horner A D S source k).1.Bounded (M*F^k) :=
    hstate.1.mono (Nat.mul_le_mul_right _ hM0)
  have hx0 : (horner A D S source k).2.Bounded (M*F^k) :=
    hstate.2.mono (Nat.mul_le_mul_right _ hM0)
  have ht : (matvec A (horner A D S source k).2).Bounded ((C*v)*F^k) := by
    convert matvec_bound hA hstate.2 using 1
    dsimp [C,F]
    ring
  have hu : (matvec A (matvec A (horner A D S source k).2)).Bounded ((C^2*v)*F^k) := by
    convert matvec_bound hA ht using 1
    dsimp [C,F]
    ring
  have hy : (inverseNumerator A D S source k).Bounded ((S*C*v)*F^k) :=
    inverseNumerator_bound hA D S source hv k
  exact ⟨bounded_fits_width hw0 hk hwidth,bounded_fits_width hx0 hk hwidth,
    bounded_fits_width (ht.mono (Nat.mul_le_mul_right _ hM1)) hk hwidth,
    bounded_fits_width (hu.mono (Nat.mul_le_mul_right _ hM2)) hk hwidth,
    bounded_fits_width (hy.mono (Nat.mul_le_mul_right _ hMS)) hk hwidth⟩

end Maxwell.Cost.CalibrationMatrix.Horner
