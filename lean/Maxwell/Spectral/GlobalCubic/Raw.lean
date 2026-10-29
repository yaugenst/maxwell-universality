import Maxwell.Spectral.Folding

namespace Maxwell.Spectral.GlobalCubic
open PeriodicYee
open PrimitiveYee (Cell Electric Face RawCell Translation rawUnit latticeVector representative)
open scoped Matrix
noncomputable section

abbrev RawField := Direction → RawCell → ℂ

def extendField (k : Momentum) (v : Electric → ℂ) : RawField :=
  fun j => PrimitiveYee.extend k (fun p => v (j,p))

theorem extend_sub (k : Momentum) (v w : Cell → ℂ) (r : RawCell) :
    PrimitiveYee.extend k (v-w) r = PrimitiveYee.extend k v r-PrimitiveYee.extend k w r := by
  simp [PrimitiveYee.extend, mul_sub]

theorem extend_shift (k : Momentum) (j : Direction) (v : Cell → ℂ) (r : RawCell) :
    PrimitiveYee.extend k (PrimitiveYee.shift k j *ᵥ v) r = PrimitiveYee.extend k v (r+rawUnit j) := by
  have h := PrimitiveYee.extend_difference k j v r
  rw [PrimitiveYee.difference_eq_shift_sub_one, Matrix.sub_mulVec, Matrix.one_mulVec, extend_sub] at h
  exact (sub_left_inj).mp h

theorem extend_shift_adjoint (k : Momentum) (j : Direction) (v : Cell → ℂ) (r : RawCell) :
    PrimitiveYee.extend k ((PrimitiveYee.shift k j).conjTranspose *ᵥ v) r =
      PrimitiveYee.extend k v (r-rawUnit j) := by
  have h := extend_shift k j ((PrimitiveYee.shift k j).conjTranspose *ᵥ v) (r-rawUnit j)
  rw [Matrix.mulVec_mulVec, PrimitiveYee.shift_mul_conjTranspose, Matrix.one_mulVec, sub_add_cancel] at h
  exact h.symm

theorem extend_difference_adjoint (k : Momentum) (j : Direction) (v : Cell → ℂ) (r : RawCell) :
    PrimitiveYee.extend k ((PrimitiveYee.difference k j).conjTranspose *ᵥ v) r =
      PrimitiveYee.extend k v (r-rawUnit j)-PrimitiveYee.extend k v r := by
  rw [PrimitiveYee.difference_eq_shift_sub_one, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.sub_mulVec, Matrix.one_mulVec, extend_sub, extend_shift_adjoint]

def derivative (j : Direction) (v : RawCell → ℂ) (r : RawCell) := v (r+rawUnit j)-v r
def adjDerivative (j : Direction) (v : RawCell → ℂ) (r : RawCell) := v (r-rawUnit j)-v r

def rawCurl (v : RawField) : RawField := fun j r =>
  if j=0 then derivative 1 (v 2) r-derivative 2 (v 1) r
  else if j=1 then derivative 2 (v 0) r-derivative 0 (v 2) r
  else derivative 0 (v 1) r-derivative 1 (v 0) r

def rawCurlAdjoint (v : RawField) : RawField := fun j r =>
  if j=0 then adjDerivative 2 (v 1) r-adjDerivative 1 (v 2) r
  else if j=1 then adjDerivative 0 (v 2) r-adjDerivative 2 (v 0) r
  else adjDerivative 1 (v 0) r-adjDerivative 0 (v 1) r

theorem extend_curl (k : Momentum) (v : Electric → ℂ) :
    extendField k (PrimitiveYee.curl k *ᵥ v) = rawCurl (extendField k v) := by
  funext j r
  fin_cases j <;>
    norm_num [extendField, PrimitiveYee.curl_mulVec, rawCurl] <;>
    rw [show (fun p => _ - _) = (fun p => _) - (fun p => _) from rfl,
      extend_sub, PrimitiveYee.extend_difference, PrimitiveYee.extend_difference] <;> rfl

theorem extend_curl_adjoint (k : Momentum) (v : Face → ℂ) :
    extendField k ((PrimitiveYee.curl k).conjTranspose *ᵥ v) = rawCurlAdjoint (extendField k v) := by
  funext j r
  fin_cases j <;>
    norm_num [extendField, PrimitiveYee.curl_adjoint_mulVec, rawCurlAdjoint] <;>
    rw [show (fun p => _ - _) = (fun p => _) - (fun p => _) from rfl,
      extend_sub, extend_difference_adjoint, extend_difference_adjoint] <;> rfl

def rawMass (material : Cell20 → ℝ) (v : RawField) : RawField := fun j r =>
  (PeriodicYee.edgeAverage material (j,PrimitiveYee.conventionalCell r) : ℂ)*v j r

def rawElectric (material : Cell20 → ℝ) (v : RawField) : RawField :=
  fun j r => rawCurlAdjoint (rawCurl v) j r - (1/64:ℂ)*rawMass material v j r

theorem extend_mass (material : Cell20 → ℝ) (hmat : Folding.FCCPeriodic material)
    (k : Momentum) (v : Electric → ℂ) :
    extendField k (PrimitiveYee.mass material *ᵥ v) = rawMass material (extendField k v) := by
  funext j r
  have hr : r = representative (PrimitiveYee.reduceCell r)+latticeVector (PrimitiveYee.reduceTranslation r) :=
    (PrimitiveYee.reconstruct_reduce r).symm
  have hm : PeriodicYee.edgeAverage material (j,PrimitiveYee.conventionalCell r) =
      PrimitiveYee.edgeAverage material (j,PrimitiveYee.reduceCell r) := by
    rw [PrimitiveYee.edgeAverage_binding, hr, Folding.edgeAverage_translate material hmat]
    rw [← hr]
  simp only [extendField, PrimitiveYee.extend, PrimitiveYee.mass, Matrix.mulVec_diagonal, rawMass, hm]
  ring

theorem extend_electric (material : Cell20 → ℝ) (hmat : Folding.FCCPeriodic material)
    (k : Momentum) (v : Electric → ℂ) :
    extendField k (PrimitiveYee.fiber material k *ᵥ v) = rawElectric material (extendField k v) := by
  have hsub (v w : Electric → ℂ) : extendField k (v-w) = extendField k v-extendField k w := by
    funext j r; exact extend_sub k _ _ r
  have hsmul (a : ℂ) (v : Electric → ℂ) : extendField k (a • v) = a • extendField k v := by
    funext j r; simp [extendField, PrimitiveYee.extend, mul_left_comm]
  rw [PrimitiveYee.fiber, Matrix.sub_mulVec, Matrix.smul_mulVec, hsub, hsmul,
    ← Matrix.mulVec_mulVec, extend_curl_adjoint, extend_curl, extend_mass material hmat]
  rfl

end
end Maxwell.Spectral.GlobalCubic
