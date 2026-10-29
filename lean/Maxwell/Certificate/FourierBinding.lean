import Maxwell.Spectral.PrimitiveYee
import Maxwell.Certificate.Trigonometric
import Maxwell.Certificate.IntervalMatrix

/-! Exact FCC Fourier symbols of the actual primitive Yee matrices.

The parameter `c` is Cartesian reciprocal momentum, as in the global
certificate's `make_d`. A plane wave includes the Bloch phase in physical
coordinates. Removing that diagonal phase gives the producer's fixed FFT. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum)

abbrev Frequency := Cell

def frequencyCoordinates (f : Frequency) : Translation :=
  ![f.1.val, f.2.1.val, f.2.2.val]

def reciprocalIndex (f : Frequency) : Translation :=
  ![f.1.val, 2 * (f.2.1.val : ℤ) - f.1.val, 2 * (f.2.2.val : ℤ) - f.1.val]

def cartesianMomentum (k : Momentum) : Momentum := ![k 0, 2 * k 1 - k 0, 2 * k 2 - k 0]

def boundaryMomentum (c : Momentum) : Momentum :=
  ![2 * Real.pi * c 0, Real.pi * (c 0 + c 1), Real.pi * (c 0 + c 2)]

theorem boundaryMomentum_cartesian (k : Momentum) :
    boundaryMomentum (cartesianMomentum k) = fun j => 2 * Real.pi * k j := by
  funext j
  fin_cases j <;> simp [boundaryMomentum, cartesianMomentum] <;> ring

def phase (c : Momentum) (f : Frequency) (r : RawCell) : ℝ :=
  (2 * Real.pi / 20) * ∑ j : Direction, ((reciprocalIndex f j : ℝ) + c j) * (r j : ℝ)

def planeWave (c : Momentum) (f : Frequency) (r : RawCell) : ℂ :=
  Complex.exp (Complex.I * (phase c f r : ℂ))

theorem phase_add (c : Momentum) (f : Frequency) (r s : RawCell) :
    phase c f (r + s) = phase c f r + phase c f s := by
  simp [phase, mul_add, Finset.sum_add_distrib]

theorem phase_lattice (c : Momentum) (f : Frequency) (t : Translation) :
    phase c f (latticeVector t) =
      (∑ j : Direction, boundaryMomentum c j * (t j : ℝ)) +
        2 * Real.pi * ((∑ j : Direction, frequencyCoordinates f j * t j : ℤ) : ℝ) := by
  simp [phase, reciprocalIndex, latticeVector, boundaryMomentum, frequencyCoordinates,
    Fin.sum_univ_three]
  ring

theorem planeWave_add (c : Momentum) (f : Frequency) (r s : RawCell) :
    planeWave c f (r + s) = planeWave c f r * planeWave c f s := by
  simp only [planeWave, phase_add, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem planeWave_lattice (c : Momentum) (f : Frequency) (t : Translation) :
    planeWave c f (latticeVector t) = character (boundaryMomentum c) t := by
  unfold planeWave
  rw [phase_lattice, Complex.ofReal_add, mul_add, Complex.exp_add]
  have he : Complex.I *
      ((2 * Real.pi * ((∑ j : Direction, frequencyCoordinates f j * t j : ℤ) : ℝ)) : ℂ) =
      (∑ j : Direction, frequencyCoordinates f j * t j : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at he ⊢
  rw [he, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp [character]

theorem planeWave_translate (c : Momentum) (f : Frequency) (r : RawCell) (t : Translation) :
    planeWave c f (r + latticeVector t) =
      character (boundaryMomentum c) t * planeWave c f r := by
  rw [planeWave_add, planeWave_lattice, mul_comm]

theorem extend_planeWave (c : Momentum) (f : Frequency) (r : RawCell) :
    extend (boundaryMomentum c) (fun p => planeWave c f (representative p)) r =
      planeWave c f r := by
  conv_rhs => rw [← reconstruct_reduce r]
  simp only [reconstruct, planeWave_translate, extend]

def shiftSymbol (c : Momentum) (f : Frequency) (j : Direction) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi / 20 * ((reciprocalIndex f j : ℝ) + c j)) : ℂ))

def symbol (c : Momentum) (f : Frequency) (j : Direction) : ℂ := shiftSymbol c f j - 1

theorem planeWave_rawUnit (c : Momentum) (f : Frequency) (j : Direction) :
    planeWave c f (rawUnit j) = shiftSymbol c f j := by
  simp [planeWave, phase, rawUnit, Pi.single_apply, mul_ite, shiftSymbol]

theorem planeWave_forward (c : Momentum) (f : Frequency) (j : Direction) (p : Cell) :
    planeWave c f (forwardRaw j p) =
      shiftSymbol c f j * planeWave c f (representative p) := by
  rw [forwardRaw, planeWave_add, planeWave_rawUnit, mul_comm]

def normalization : ℂ := ((Real.sqrt 2000 : ℝ) : ℂ)⁻¹

def basis (c : Momentum) (f : Frequency) (p : Cell) : ℂ :=
  normalization * planeWave c f (representative p)

def transform (c : Momentum) : Matrix Cell Frequency ℂ := fun p f => basis c f p

theorem shift_basis (c : Momentum) (f : Frequency) (j : Direction) (p : Cell) :
    (shift (boundaryMomentum c) j *ᵥ basis c f) p = shiftSymbol c f j * basis c f p := by
  have he := extend_planeWave c f (forwardRaw j p)
  change boundaryPhase (boundaryMomentum c) j p *
      planeWave c f (representative (forwardCell j p)) = planeWave c f (forwardRaw j p) at he
  rw [planeWave_forward] at he
  simp only [shift, Matrix.mulVec, dotProduct, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  dsimp [basis]
  calc
    _ = normalization * (boundaryPhase (boundaryMomentum c) j p *
        planeWave c f (representative (forwardCell j p))) := by ring
    _ = _ := by rw [he]; ring

theorem difference_basis (c : Momentum) (f : Frequency) (j : Direction) (p : Cell) :
    (difference (boundaryMomentum c) j *ᵥ basis c f) p = symbol c f j * basis c f p := by
  rw [difference_eq_shift_sub_one, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, shift_basis, symbol]
  ring

theorem difference_transform (c : Momentum) (j : Direction) :
    difference (boundaryMomentum c) j * transform c =
      transform c * Matrix.diagonal (fun f => symbol c f j) := by
  ext p f
  rw [Matrix.mul_diagonal]
  simpa only [Matrix.mul_apply, transform, Matrix.mulVec, dotProduct, mul_comm] using
    difference_basis c f j p

def polarizedBasis (c : Momentum) (f : Frequency) (a : Direction → ℂ) : Electric → ℂ :=
  fun e => a e.1 * basis c f e.2

def crossSymbol (c : Momentum) (f : Frequency) (a : Direction → ℂ) : Direction → ℂ :=
  ![symbol c f 1 * a 2 - symbol c f 2 * a 1,
    symbol c f 2 * a 0 - symbol c f 0 * a 2,
    symbol c f 0 * a 1 - symbol c f 1 * a 0]

theorem difference_polarized (c : Momentum) (f : Frequency) (a : ℂ) (j : Direction)
    (p : Cell) :
    (difference (boundaryMomentum c) j *ᵥ fun q => a * basis c f q) p =
      a * symbol c f j * basis c f p := by
  have he : (fun q => a * basis c f q) = a • basis c f := rfl
  rw [he, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, difference_basis]
  ring

theorem curl_polarizedBasis (c : Momentum) (f : Frequency) (a : Direction → ℂ) :
    curl (boundaryMomentum c) *ᵥ polarizedBasis c f a =
      polarizedBasis c f (crossSymbol c f a) := by
  funext e
  rcases e with ⟨j, p⟩
  rw [curl_mulVec]
  fin_cases j <;>
    simp [polarizedBasis, crossSymbol, difference_polarized] <;> ring

def electricTransform (c : Momentum) : Matrix Electric Electric ℂ :=
  fun e f => if e.1 = f.1 then basis c f.2 e.2 else 0

def curlSymbolMatrix (c : Momentum) (f : Frequency) : Matrix Direction Direction ℂ :=
  !![0, -symbol c f 2, symbol c f 1;
     symbol c f 2, 0, -symbol c f 0;
     -symbol c f 1, symbol c f 0, 0]

def frequencyCurl (c : Momentum) : Matrix Electric Electric ℂ :=
  fun e f => if e.2 = f.2 then curlSymbolMatrix c e.2 e.1 f.1 else 0

theorem curl_transform (c : Momentum) :
    curl (boundaryMomentum c) * electricTransform c = electricTransform c * frequencyCurl c := by
  ext ⟨i, p⟩ ⟨j, f⟩
  have hd := fun d => difference_transform c d
  have he d := congrFun (congrFun (hd d) p) f
  simp only [Matrix.mul_diagonal] at he
  fin_cases i <;> fin_cases j <;>
    simp [curl, electricTransform, frequencyCurl, curlSymbolMatrix, Matrix.mul_apply,
      Fintype.sum_prod_type, ite_mul, mul_ite, transform] at he ⊢ <;>
    exact he _

theorem shiftSymbol_eq_cis (c : Direction → ℚ) (f : Frequency) (j : Direction) :
    shiftSymbol (fun d => (c d : ℝ)) f j =
      Trigonometric.cis (((reciprocalIndex f j : ℚ) + c j) / 20) := by
  unfold shiftSymbol Trigonometric.cis
  congr 1
  push_cast
  ring

theorem cis_add (a b : ℚ) :
    Trigonometric.cis (a + b) = Trigonometric.cis a * Trigonometric.cis b := by
  unfold Trigonometric.cis
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem cis_add_int (a : ℚ) (n : ℤ) :
    Trigonometric.cis (a + (n : ℚ)) = Trigonometric.cis a := by
  rw [cis_add]
  have hn : Trigonometric.cis (n : ℚ) = 1 := by
    unfold Trigonometric.cis
    have he : Complex.I * ((2 * Real.pi * ((n : ℚ) : ℝ)) : ℂ) =
        (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_int_mul_two_pi_mul_I]
  rw [hn, mul_one]

theorem shiftSymbol_factorization (c : Direction → ℚ) (f : Frequency) (j : Direction) :
    shiftSymbol (fun d => (c d : ℝ)) f j =
      Trigonometric.cis (((reciprocalIndex f j % 20 : ℤ) : ℚ) / 20) *
        Trigonometric.cis (c j / 20) := by
  rw [shiftSymbol_eq_cis, add_div, cis_add]
  have hq : (reciprocalIndex f j : ℚ) / 20 =
      ((reciprocalIndex f j % 20 : ℤ) : ℚ) / 20 +
        ((reciprocalIndex f j / 20 : ℤ) : ℚ) := by
    have hZ : reciprocalIndex f j % 20 + 20 * (reciprocalIndex f j / 20) =
        reciprocalIndex f j := by omega
    have hi := congrArg ((↑) : ℤ → ℚ) hZ
    push_cast at hi
    linarith
  rw [hq, cis_add_int]

def oneRectangle : ComplexRectangle :=
  IntervalMatrix.realRectangle ⟨1, 0, le_rfl⟩

theorem oneRectangle_contains : oneRectangle.Contains 1 := by
  exact IntervalMatrix.realRectangle_contains (by simp [Ball.Contains])

/-- This is the exact algebra used by `make_d`: a root of unity times a
Cartesian Bloch phase, minus one. -/
def symbolRectangle (c : Direction → ℚ) (f : Frequency) (j : Direction) : ComplexRectangle :=
  IntervalMatrix.subRectangle
    ((Trigonometric.cisRectangle (((reciprocalIndex f j % 20 : ℤ) : ℚ) / 20)).mul
      (Trigonometric.cisRectangle (c j / 20))) oneRectangle

theorem symbolRectangle_contains (c : Direction → ℚ) (f : Frequency) (j : Direction) :
    (symbolRectangle c f j).Contains (symbol (fun d => (c d : ℝ)) f j) := by
  unfold symbol
  rw [shiftSymbol_factorization]
  exact IntervalMatrix.subRectangle_contains
    (ComplexRectangle.contains_mul (Trigonometric.cisRectangle_contains _)
      (Trigonometric.cisRectangle_contains _)) oneRectangle_contains

theorem proposed_symbol_contains (c : Direction → ℚ) (f : Frequency) (j : Direction)
    (root phase : ComplexRectangle)
    (hr : Trigonometric.cisCheck (((reciprocalIndex f j % 20 : ℤ) : ℚ) / 20) root = true)
    (hp : Trigonometric.cisCheck (c j / 20) phase = true) :
    (IntervalMatrix.subRectangle (root.mul phase) oneRectangle).Contains
      (symbol (fun d => (c d : ℝ)) f j) := by
  unfold symbol
  rw [shiftSymbol_factorization]
  exact IntervalMatrix.subRectangle_contains
    (ComplexRectangle.contains_mul (Trigonometric.cisCheck_sound hr)
      (Trigonometric.cisCheck_sound hp)) oneRectangle_contains

end Maxwell.Certificate.FourierBinding
