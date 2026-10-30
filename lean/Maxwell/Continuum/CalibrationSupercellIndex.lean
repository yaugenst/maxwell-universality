import Maxwell.Continuum.CalibrationCenteredGrid
import Maxwell.Continuum.CalibrationAliasSupport

/-! Exact integer indexing of a period-2M Fourier mode by its centered
Bloch-grid point and complete period-two alias. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber

variable (M : ℕ) [NeZero M]

def centeredOffset (j : ZMod M) : ℤ :=
  if 2*j.val≤M then (j.val : ℤ) else (j.val : ℤ)-M

theorem centeredOffset_cast (j : ZMod M) : (centeredOffset M j : ZMod M)=j := by
  unfold centeredOffset
  split_ifs <;> simp

theorem centeredOffset_rational (j : ZMod M) :
    (centeredOffset M j : ℚ)=(M : ℚ)*centeredGrid M j := by
  have hM : (M : ℚ)≠0 := by exact_mod_cast NeZero.ne M
  unfold centeredOffset centeredGrid gridTurn
  split_ifs <;> push_cast <;> field_simp

def joinCoordinate (p : ZMod M × ℤ) : ℤ := (M : ℤ)*p.2+(M/2 : ℕ)+centeredOffset M p.1

def splitCoordinate (n : ℤ) : ZMod M × ℤ :=
  let q := n-(M/2 : ℕ)
  let j : ZMod M := q
  (j,(q-centeredOffset M j)/(M : ℤ))

theorem centeredOffset_sub_dvd (q : ℤ) : (M : ℤ) ∣ q-centeredOffset M (q : ZMod M) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
  rw [Int.cast_sub,centeredOffset_cast,sub_self]

theorem join_split (n : ℤ) : joinCoordinate M (splitCoordinate M n)=n := by
  change (M : ℤ)*((n-(M/2 : ℕ)-centeredOffset M ((n-(M/2 : ℕ) : ℤ) : ZMod M))/M)+
    (M/2 : ℕ)+centeredOffset M ((n-(M/2 : ℕ) : ℤ) : ZMod M)=n
  rw [Int.mul_ediv_cancel' (centeredOffset_sub_dvd M (n-(M/2 : ℕ)))]
  ring

theorem split_join (p : ZMod M × ℤ) : splitCoordinate M (joinCoordinate M p)=p := by
  have hM : (M : ℤ)≠0 := by exact_mod_cast NeZero.ne M
  have hgrid : ((joinCoordinate M p-(M/2 : ℕ) : ℤ) : ZMod M)=p.1 := by
    simp only [joinCoordinate,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast,
      ZMod.natCast_self,zero_mul,zero_add,centeredOffset_cast,add_sub_cancel_left]
  apply Prod.ext
  · exact hgrid
  · change (joinCoordinate M p-(M/2 : ℕ)-centeredOffset M
      ((joinCoordinate M p-(M/2 : ℕ) : ℤ) : ZMod M))/(M : ℤ)=p.2
    rw [hgrid]
    have he : joinCoordinate M p-(M/2 : ℕ)-centeredOffset M p.1=(M : ℤ)*p.2 := by
      unfold joinCoordinate
      ring
    rw [he,Int.mul_ediv_cancel_left _ hM]

def coordinateEquiv : (ZMod M × ℤ) ≃ ℤ where
  toFun := joinCoordinate M
  invFun := splitCoordinate M
  left_inv := split_join M
  right_inv := join_split M

abbrev Grid := Fin 3 → ZMod M

def join (p : Grid M × Alias) : Alias := fun i => joinCoordinate M (p.1 i,p.2 i)
def split (n : Alias) : Grid M × Alias :=
  (fun i => (splitCoordinate M (n i)).1,fun i => (splitCoordinate M (n i)).2)

def indexEquiv : (Grid M × Alias) ≃ Alias where
  toFun := join M
  invFun := split M
  left_inv p := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst (split_join M (p.1 i,p.2 i))
    · exact congrArg Prod.snd (split_join M (p.1 i,p.2 i))
  right_inv n := by
    funext i
    exact join_split M (n i)

omit [NeZero M] in
theorem half_even (hEven : Even M) : ((M/2 : ℕ) : ℝ)=(M : ℝ)/2 := by
  have h := Nat.mul_div_cancel' (even_iff_two_dvd.mp hEven)
  have hr : (2 : ℝ)*((M/2 : ℕ) : ℝ)=(M : ℝ) := by exact_mod_cast h
  linarith

theorem join_wavevector (hEven : Even M) (j : Grid M) (ν : Alias) (i : Fin 3) :
    Real.pi*(join M (j,ν) i : ℝ)/(M : ℝ)=
      Real.pi*((ν i : ℝ)+1/2+(centeredGrid M (j i) : ℝ)) := by
  have hM : (M : ℝ)≠0 := by exact_mod_cast NeZero.ne M
  have ho : (centeredOffset M (j i) : ℝ)=(M : ℝ)*(centeredGrid M (j i) : ℝ) := by
    exact_mod_cast centeredOffset_rational M (j i)
  change Real.pi*(joinCoordinate M (j i,ν i) : ℝ)/(M : ℝ)=_
  simp only [joinCoordinate,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  rw [half_even M hEven,ho]
  field_simp

#print axioms indexEquiv
#print axioms join_wavevector

end Maxwell.Continuum.Calibration.Supercell
