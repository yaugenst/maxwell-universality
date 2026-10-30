import Maxwell.Continuum.CalibrationRationalMatrix
import Init.Data.Vector.OfFn

/-! Executable dense-array indexing of a finite alias cube, with an
exact zero extension and no noncomputable enumeration. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def aliasSide (R : ℕ) : ℕ := 2*R+1
abbrev AliasArrayIndex (R : ℕ) := (Fin (aliasSide R) × Fin (aliasSide R) × Fin (aliasSide R)) × Fin 3
def aliasArraySize (R : ℕ) : ℕ := (aliasSide R*(aliasSide R*aliasSide R))*3

def aliasArrayEquiv (R : ℕ) : AliasArrayIndex R ≃ Fin (aliasArraySize R) :=
  (Equiv.prodCongr
    ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)
    (Equiv.refl _)).trans finProdFinEquiv

def arrayAlias (R : ℕ) (i : Fin (aliasSide R) × Fin (aliasSide R) × Fin (aliasSide R)) : Alias :=
  fun j => ((![i.1.val,i.2.1.val,i.2.2.val] j : ℕ) : ℤ)-(R : ℤ)

def aliasInCube (R : ℕ) (ν : Alias) : Prop := ∀ j, |ν j| ≤ (R : ℤ)

instance (R : ℕ) (ν : Alias) : Decidable (aliasInCube R ν) :=
  inferInstanceAs (Decidable (∀ j : Fin 3, |ν j| ≤ (R : ℤ)))

def arrayCoordinate (R : ℕ) (ν : Alias) (hν : aliasInCube R ν) (j : Fin 3) : Fin (aliasSide R) :=
  ⟨(ν j+(R : ℤ)).toNat, by
    have hj := abs_le.mp (hν j)
    unfold aliasSide
    omega⟩

def arrayAliasIndex (R : ℕ) (ν : Alias) (hν : aliasInCube R ν) :
    Fin (aliasSide R) × Fin (aliasSide R) × Fin (aliasSide R) :=
  (arrayCoordinate R ν hν 0,arrayCoordinate R ν hν 1,arrayCoordinate R ν hν 2)

theorem arrayAlias_mem (R : ℕ) (i : Fin (aliasSide R) × Fin (aliasSide R) × Fin (aliasSide R)) :
    aliasInCube R (arrayAlias R i) := by
  intro j
  have h0 := i.1.isLt
  have h1 := i.2.1.isLt
  have h2 := i.2.2.isLt
  unfold aliasSide at h0 h1 h2
  fin_cases j <;> norm_num [arrayAlias]
  all_goals rw [abs_le]; constructor <;> omega

theorem arrayAlias_index (R : ℕ) (ν : Alias) (hν : aliasInCube R ν) :
    arrayAlias R (arrayAliasIndex R ν hν) = ν := by
  funext j
  have hj := abs_le.mp (hν j)
  fin_cases j <;> norm_num [arrayAlias,arrayAliasIndex,arrayCoordinate] at hj ⊢
  all_goals omega

theorem arrayIndex_alias (R : ℕ) (i : Fin (aliasSide R) × Fin (aliasSide R) × Fin (aliasSide R)) :
    arrayAliasIndex R (arrayAlias R i) (arrayAlias_mem R i) = i := by
  apply Prod.ext
  · apply Fin.ext
    norm_num [arrayAliasIndex,arrayCoordinate,arrayAlias]
  · apply Prod.ext <;> apply Fin.ext
    · norm_num [arrayAliasIndex,arrayCoordinate,arrayAlias]
    · norm_num [arrayAliasIndex,arrayCoordinate,arrayAlias]

def sampleAliasArray {V : Type*} (R : ℕ) (f : Alias → Fin 3 → V) : Vector V (aliasArraySize R) :=
  Vector.ofFn (fun i => f (arrayAlias R (aliasArrayEquiv R |>.symm i).1) (aliasArrayEquiv R |>.symm i).2)

def extendAliasArray {V : Type*} [Zero V] (R : ℕ) (a : Vector V (aliasArraySize R)) : Alias → Fin 3 → V :=
  fun ν j => if hν : aliasInCube R ν then
    a.get (aliasArrayEquiv R (arrayAliasIndex R ν hν,j)) else 0

theorem vector_get_ofFn {V : Type*} {n : ℕ} (f : Fin n → V) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  convert! Array.getElem_ofFn (f := f) (i := i.val) (by simp) using 1

theorem extend_sample_alias {V : Type*} [Zero V] (R : ℕ) (f : Alias → Fin 3 → V)
    (ν : Alias) (j : Fin 3) :
    extendAliasArray R (sampleAliasArray R f) ν j = if aliasInCube R ν then f ν j else 0 := by
  unfold extendAliasArray
  split_ifs with hν
  · rw [sampleAliasArray,vector_get_ofFn]
    simp only [Equiv.symm_apply_apply,arrayAlias_index]
  · rfl

#print axioms extend_sample_alias

end Maxwell.Continuum.Calibration
