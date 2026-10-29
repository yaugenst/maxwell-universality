import Maxwell.Certificate.SparseAction
import Mathlib.Algebra.Ring.Int.Parity

namespace Maxwell.Certificate.PrimitiveBinding
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Cell20 transverseDirections)

def phaseI (k : Translation) (j : Direction) (p : Cell) : ℤ :=
  if Even (∑ a, k a * reduceTranslation (forwardRaw j p) a) then 1 else -1

def differenceActionI (k : Translation) (j : Direction) (v : Cell → ℤ) (p : Cell) : ℤ :=
  phaseI k j p * v (forwardCell j p) - v p

def differenceTransposeActionI (k : Translation) (j : Direction) (v : Cell → ℤ) (p : Cell) : ℤ :=
  phaseI k j (backwardCell j p) * v (backwardCell j p) - v p

def curlActionI (k : Translation) (v : Electric → ℤ) (e : Electric) : ℤ :=
  if e.1 = 0 then
    differenceActionI k 1 (fun p => v (2,p)) e.2 - differenceActionI k 2 (fun p => v (1,p)) e.2
  else if e.1 = 1 then
    differenceActionI k 2 (fun p => v (0,p)) e.2 - differenceActionI k 0 (fun p => v (2,p)) e.2
  else
    differenceActionI k 0 (fun p => v (1,p)) e.2 - differenceActionI k 1 (fun p => v (0,p)) e.2

def curlTransposeActionI (k : Translation) (v : Face → ℤ) (e : Electric) : ℤ :=
  if e.1 = 0 then
    differenceTransposeActionI k 2 (fun p => v (1,p)) e.2 -
      differenceTransposeActionI k 1 (fun p => v (2,p)) e.2
  else if e.1 = 1 then
    differenceTransposeActionI k 0 (fun p => v (2,p)) e.2 -
      differenceTransposeActionI k 2 (fun p => v (0,p)) e.2
  else
    differenceTransposeActionI k 1 (fun p => v (0,p)) e.2 -
      differenceTransposeActionI k 0 (fun p => v (1,p)) e.2

noncomputable def cellNumerator (r : Cell20) : ℤ :=
  let c := Concrete.cellCoordinate r
  (if Material.inDiamond c then 12 else 1) * 2097152 +
    Material.numerator (c 0) (c 1) (c 2)

noncomputable def massNumerator (e : Electric) : ℤ :=
  let p := transverseDirections e.1
  let r := representative e.2
  cellNumerator (conventionalCell r) + cellNumerator (conventionalCell (r - rawUnit p.1)) +
    cellNumerator (conventionalCell (r - rawUnit p.2)) +
    cellNumerator (conventionalCell (r - rawUnit p.1 - rawUnit p.2))

noncomputable def fiberActionI (k : Translation) (v : Electric → ℤ) (e : Electric) : ℤ :=
  536870912 * curlTransposeActionI k (curlActionI k v) e - massNumerator e * v e

noncomputable section

theorem phaseI_cast (k : Translation) (j : Direction) (p : Cell) :
    (phaseI k j p : ℚ) = phaseQ k j p := by
  simp only [phaseI, phaseQ, neg_one_zpow_eq_ite]
  split_ifs <;> norm_num

theorem differenceActionI_cast (k : Translation) (j : Direction) (v : Cell → ℤ)
    (d : ℚ) (p : Cell) :
    differenceActionQ k j (fun p => (v p : ℚ) / d) p = (differenceActionI k j v p : ℚ) / d := by
  simp only [differenceActionQ, differenceActionI, Int.cast_sub, Int.cast_mul, phaseI_cast]
  ring

theorem differenceTransposeActionI_cast (k : Translation) (j : Direction) (v : Cell → ℤ)
    (d : ℚ) (p : Cell) :
    differenceTransposeActionQ k j (fun p => (v p : ℚ) / d) p =
      (differenceTransposeActionI k j v p : ℚ) / d := by
  simp only [differenceTransposeActionQ, differenceTransposeActionI, Int.cast_sub, Int.cast_mul, phaseI_cast]
  ring

theorem curlActionI_cast (k : Translation) (v : Electric → ℤ) (d : ℚ) (e : Electric) :
    curlActionQ k (fun e => (v e : ℚ) / d) e = (curlActionI k v e : ℚ) / d := by
  unfold curlActionQ curlActionI
  split_ifs <;> simp only [differenceActionI_cast, Int.cast_sub] <;> ring

theorem curlTransposeActionI_cast (k : Translation) (v : Face → ℤ) (d : ℚ) (e : Electric) :
    curlTransposeActionQ k (fun e => (v e : ℚ) / d) e = (curlTransposeActionI k v e : ℚ) / d := by
  unfold curlTransposeActionQ curlTransposeActionI
  split_ifs <;> simp only [differenceTransposeActionI_cast, Int.cast_sub] <;> ring

theorem cellNumerator_cast (r : Cell20) : materialQ r = (cellNumerator r : ℚ) / 2097152 := by
  unfold materialQ cellNumerator Material.cellValue Material.baseValue
  split_ifs <;> push_cast <;> simp_all <;> ring

theorem massNumerator_cast (e : Electric) : edgeAverageQ e = (massNumerator e : ℚ) / 8388608 := by
  simp only [edgeAverageQ, massNumerator, cellNumerator_cast, Int.cast_add]
  ring

/-- Checking the integer action is sufficient for the exact rational
matrix action at any nonzero vector denominator. The scale `2^29` is the
four-cell averaging, material denominator, and frequency squared combined. -/
theorem fiberActionI_cast (k : Translation) (v : Electric → ℤ) (d : ℚ) (hd : d ≠ 0)
    (e : Electric) :
    fiberActionQ k (fun e => (v e : ℚ) / d) e = (fiberActionI k v e : ℚ) / (536870912 * d) := by
  have hc : curlActionQ k (fun e => (v e : ℚ) / d) =
      fun e => (curlActionI k v e : ℚ) / d := funext (curlActionI_cast k v d)
  simp only [fiberActionQ, hc, curlTransposeActionI_cast, massNumerator_cast,
    fiberActionI, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  field_simp; ring

end
end Maxwell.Certificate.PrimitiveBinding
