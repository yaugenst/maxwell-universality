import Maxwell.Certificate.FourierUnitary

/-! The certificate producer uses a fixed FFT and puts Bloch momentum in
the difference symbols. The physical boundary-gauge transform differs by
the diagonal phase below, which cancels from every material diagonal. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum Cell20)

def zeroFrequency : Frequency := (0, 0, 0)

theorem phase_decomposition (c : Momentum) (f : Frequency) (r : RawCell) :
    phase c f r = phase c zeroFrequency r + phase 0 f r := by
  simp [phase, reciprocalIndex, zeroFrequency, Fin.sum_univ_three]
  ring

theorem planeWave_decomposition (c : Momentum) (f : Frequency) (r : RawCell) :
    planeWave c f r = planeWave c zeroFrequency r * planeWave 0 f r := by
  rw [planeWave, phase_decomposition]
  simp only [planeWave, Complex.ofReal_add, mul_add, Complex.exp_add]

def spatialGauge (c : Momentum) (p : Cell) : ℂ :=
  planeWave c zeroFrequency (representative p)

theorem spatialGauge_unit (c : Momentum) (p : Cell) :
    star (spatialGauge c p) * spatialGauge c p = 1 := planeWave_unit _ _ _

theorem basis_gauge (c : Momentum) (f : Frequency) (p : Cell) :
    basis c f p = spatialGauge c p * basis 0 f p := by
  unfold basis spatialGauge
  rw [planeWave_decomposition]
  ring

theorem transform_gauge (c : Momentum) :
    transform c = Matrix.diagonal (spatialGauge c) * transform 0 := by
  ext p f
  rw [Matrix.diagonal_mul]
  exact basis_gauge c f p

def electricGauge (c : Momentum) : Matrix Electric Electric ℂ :=
  Matrix.diagonal fun e => spatialGauge c e.2

theorem electricTransform_gauge (c : Momentum) :
    electricTransform c = electricGauge c * electricTransform 0 := by
  ext e f
  simp only [electricGauge, Matrix.diagonal_mul, electricTransform]
  split_ifs
  · exact basis_gauge c f.2 e.2
  · simp only [mul_zero]

theorem electricGauge_diagonal (c : Momentum) (d : Electric → ℂ) :
    (electricGauge c).conjTranspose * Matrix.diagonal d * electricGauge c =
      Matrix.diagonal d := by
  simp only [electricGauge, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext e
  change star (spatialGauge c e.2) * d e * spatialGauge c e.2 = d e
  calc
    _ = d e * (star (spatialGauge c e.2) * spatialGauge c e.2) := by ring
    _ = _ := by rw [spatialGauge_unit, mul_one]

theorem diagonal_compression_eq_zero (c : Momentum) (d : Electric → ℂ) :
    (electricTransform c).conjTranspose * Matrix.diagonal d * electricTransform c =
      (electricTransform 0).conjTranspose * Matrix.diagonal d * electricTransform 0 := by
  calc
    _ = (electricTransform 0).conjTranspose *
        ((electricGauge c).conjTranspose * Matrix.diagonal d * electricGauge c) *
          electricTransform 0 := by
      rw [electricTransform_gauge, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [electricGauge_diagonal]

theorem fourierMass_eq_zero (material : Cell20 → ℝ) (c : Momentum) :
    fourierMass material c = fourierMass material 0 :=
  diagonal_compression_eq_zero c _

/-- The exact electric fiber in the fixed Fourier coordinates used by the
producer. Only the curl symbol depends on Bloch momentum. -/
theorem fiber_fixed_fourier (material : Cell20 → ℝ) (c : Momentum) :
    (electricTransform c).conjTranspose * fiber material (boundaryMomentum c) *
        electricTransform c =
      (frequencyCurl c).conjTranspose * frequencyCurl c -
        (1 / 64 : ℂ) • fourierMass material 0 := by
  rw [fiber_diagonalized, fourierFiber, fourierMass_eq_zero]

def inverseMass (material : Cell20 → ℝ) : Matrix Electric Electric ℂ :=
  Matrix.diagonal fun e => ((edgeAverage material e : ℂ))⁻¹

def magneticFiber (material : Cell20 → ℝ) (k : Momentum) : Matrix Electric Electric ℂ :=
  curl k * inverseMass material * (curl k).conjTranspose - (1 / 64 : ℂ) • (1 : Matrix Electric Electric ℂ)

def fourierInverseMass (material : Cell20 → ℝ) : Matrix Electric Electric ℂ :=
  (electricTransform 0).conjTranspose * inverseMass material * electricTransform 0

theorem magneticFiber_fixed_fourier (material : Cell20 → ℝ) (c : Momentum) :
    (electricTransform c).conjTranspose * magneticFiber material (boundaryMomentum c) *
        electricTransform c =
      frequencyCurl c * fourierInverseMass material * (frequencyCurl c).conjTranspose -
        (1 / 64 : ℂ) • (1 : Matrix Electric Electric ℂ) := by
  unfold magneticFiber fourierInverseMass
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, electricTransform_conjTranspose_mul]
  rw [unitary_compression_mul _ _ _ (electricTransform_mul_conjTranspose c),
    unitary_compression_mul _ _ _ (electricTransform_mul_conjTranspose c),
    curl_diagonalized, curl_adjoint_diagonalized]
  rw [inverseMass, diagonal_compression_eq_zero]

end Maxwell.Certificate.FourierBinding
