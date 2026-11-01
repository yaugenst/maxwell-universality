import Maxwell.Continuum.CalibrationFiniteSeedSparse
import Maxwell.Continuum.CalibrationRootFrequency

/-! Natural offsets and cache indices for the eight seed contributions.
The support check uses six ordered natural comparisons; subtraction is only
used after these comparisons establish that its result is exact. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open FreeFiber PeriodicSampling RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def base (M : ℕ) (s : Corner.Parity) (j : Fin 3) : ℕ :=
  (if ![s.1,s.2.1,s.2.2] j then 3 else 2)*M+M/2

theorem base_alias (M : ℕ) [NeZero M] (s : Corner.Parity) (j : Fin 3) :
    (base M s j:ℤ)=3*M+Supercell.seedAlias M s j := by
  unfold base Supercell.seedAlias Supercell.join Supercell.joinCoordinate
    Supercell.centeredOffset rationalCubeAlias
  simp only [Pi.zero_apply,ZMod.val_zero,mul_zero,zero_le,ite_true,Int.natCast_zero,add_zero]
  split_ifs <;> push_cast <;> ring

def inside (M D : ℕ) (s : Corner.Parity) (u : Fin 3→ℕ) : Prop :=
  ∀j,base M s j≤u j ∧ u j≤base M s j+2*D

instance (M D : ℕ) (s : Corner.Parity) (u : Fin 3→ℕ) : Decidable (inside M D s u) :=
  inferInstanceAs (Decidable (∀j,base M s j≤u j ∧ u j≤base M s j+2*D))

def outputAlias (M D : ℕ) (u : Fin 3→ℕ) : Alias := fun j => (u j:ℤ)-(3*M+D:ℕ)
def digit (M : ℕ) (s : Corner.Parity) (u : Fin 3→ℕ) (j : Fin 3) : ℕ := u j-base M s j
def flat (grid : ℕ) (x : Fin 3→ℕ) : ℕ := x 0+grid*(x 1+grid*x 2)
def index (M D : ℕ) (s : Corner.Parity) (u : Fin 3→ℕ) (part : Fin 2) : ℕ :=
  2*flat (2*D+1) (digit M s u)+part.val

theorem inside_iff (M D : ℕ) [NeZero M] (s : Corner.Parity) (u : Fin 3→ℕ) :
    inside M D s u ↔ outputAlias M D u-Supercell.seedAlias M s∈Product.frequencyCube D := by
  rw [Product.mem_frequencyCube]
  constructor
  · intro h j
    have hh := h j
    have hb := base_alias M s j
    simp only [Pi.sub_apply,outputAlias,Int.natCast_add,Int.natCast_mul,Nat.cast_ofNat]
    rw [abs_le]
    constructor <;> omega
  · intro h j
    have hh := h j
    have hb := base_alias M s j
    simp only [Pi.sub_apply,outputAlias,Int.natCast_add,Int.natCast_mul,Nat.cast_ofNat] at hh
    rw [abs_le] at hh
    omega

theorem digit_lt (M D : ℕ) (s : Corner.Parity) (u : Fin 3→ℕ)
    (h : inside M D s u) (j : Fin 3) : digit M s u j<2*D+1 := by
  have hh := h j
  unfold digit
  omega

theorem flat_lt (grid : ℕ) (x : Fin 3→ℕ) (h : ∀j,x j<grid) : flat grid x<grid^3 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hy : x 1+grid*x 2<grid^2 := by nlinarith
  unfold flat
  nlinarith

theorem flat_digits (grid : ℕ) (x : Fin 3→ℕ) (h : ∀j,x j<grid) :
    RootGrid.digits grid (flat grid x)=x := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hg : 0<grid := by omega
  have q0 : flat grid x/grid=x 1+grid*x 2 := by
    simp [flat,Nat.add_mul_div_left,Nat.div_eq_of_lt h0,hg]
  have q1 : (x 1+grid*x 2)/grid=x 2 := by
    simp [Nat.add_mul_div_left,Nat.div_eq_of_lt h1,hg]
  funext j
  fin_cases j
  · simp [RootGrid.digits,flat,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h0]
  · simp [RootGrid.digits,q0,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h1]
  · simp [RootGrid.digits,q0,q1,Nat.mod_eq_of_lt h2]

theorem index_lt (M D : ℕ) (s : Corner.Parity) (u : Fin 3→ℕ) (part : Fin 2)
    (h : inside M D s u) : index M D s u part<2*(2*D+1)^3 := by
  have hf := flat_lt (2*D+1) (digit M s u) (digit_lt M D s u h)
  have hp := part.isLt
  unfold index
  omega

theorem index_part (M D : ℕ) (s : Corner.Parity) (u : Fin 3→ℕ) (part : Fin 2) :
    index M D s u part%2=part.val := by
  have hp := part.isLt
  unfold index
  omega

theorem index_frequency (M D : ℕ) [NeZero M] (s : Corner.Parity) (u : Fin 3→ℕ)
    (part : Fin 2) (h : inside M D s u) :
    RootFrequency.frequency (2*D+1) (index M D s u part)=
      outputAlias M D u-Supercell.seedAlias M s := by
  have hp := part.isLt
  have hi : index M D s u part/2=flat (2*D+1) (digit M s u) := by unfold index;omega
  unfold RootFrequency.frequency
  rw [hi,flat_digits _ _ (digit_lt M D s u h)]
  funext j
  have hb := base_alias M s j
  have hh := h j
  simp only [digit,outputAlias,Pi.sub_apply,Int.natCast_add,Int.natCast_mul,Nat.cast_ofNat]
  omega

#print axioms inside_iff
#print axioms index_frequency
end Maxwell.Continuum.Calibration.SeedRoot
