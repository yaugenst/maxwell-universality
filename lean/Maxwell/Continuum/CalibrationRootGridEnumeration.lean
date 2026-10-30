import Maxwell.Continuum.CalibrationRootGridIndex

/-! The executed mixed-radix index enumerates every root quadrature point
once, with the exact reduced phase used by the finite DFT. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost
set_option maxHeartbeats 2500000

def point (grid index : ℕ) : Fin 3→ZMod grid := fun i => (digits grid index i : ZMod grid)
def pack (grid : ℕ) (j : Fin 3→ZMod grid) : ℕ :=
  (j 0).val+grid*((j 1).val+grid*(j 2).val)

theorem point_val (grid : ℕ) [NeZero grid] (index : ℕ) (i : Fin 3) :
    (point grid index i).val=digits grid index i :=
  ZMod.val_natCast_of_lt (digits_lt (Nat.pos_of_ne_zero (NeZero.ne grid)) index i)

theorem pack_lt (grid : ℕ) [NeZero grid] (j : Fin 3→ZMod grid) : pack grid j<grid^3 := by
  have h0 := ZMod.val_lt (j 0)
  have h1 := ZMod.val_lt (j 1)
  have h2 := ZMod.val_lt (j 2)
  have hinner : (j 1).val+grid*(j 2).val<grid*grid := by nlinarith
  unfold pack
  nlinarith

theorem digits_pack (grid : ℕ) [NeZero grid] (j : Fin 3→ZMod grid) (i : Fin 3) :
    digits grid (pack grid j) i=(j i).val := by
  have hg : 0<grid := Nat.pos_of_ne_zero (NeZero.ne grid)
  have h0 := ZMod.val_lt (j 0)
  have h1 := ZMod.val_lt (j 1)
  have h2 := ZMod.val_lt (j 2)
  fin_cases i
  · change ((j 0).val+grid*((j 1).val+grid*(j 2).val))%grid=(j 0).val
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h0]
  · change ((j 0).val+grid*((j 1).val+grid*(j 2).val))/grid%grid=(j 1).val
    simp only [Nat.add_mul_div_left _ _ hg,
      Nat.div_eq_of_lt h0,zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h1]
  · change ((j 0).val+grid*((j 1).val+grid*(j 2).val))/grid/grid%grid=(j 2).val
    simp only [Nat.add_mul_div_left _ _ hg,Nat.div_eq_of_lt h0,Nat.div_eq_of_lt h1,
      zero_add,Nat.mod_eq_of_lt h2]

theorem point_pack (grid : ℕ) [NeZero grid] (j : Fin 3→ZMod grid) : point grid (pack grid j)=j := by
  funext i
  rw [point,digits_pack,ZMod.natCast_zmod_val]

theorem pack_point (grid : ℕ) [NeZero grid] (k : Fin (grid^3)) : pack grid (point grid k)=k.val := by
  have hg : 0<grid := Nat.pos_of_ne_zero (NeZero.ne grid)
  have hq : k.val/grid<grid*grid := (Nat.div_lt_iff_lt_mul hg).mpr (by
    have hk := k.isLt
    nlinarith)
  have hqq : k.val/grid/grid<grid := (Nat.div_lt_iff_lt_mul hg).mpr hq
  simp only [pack,point_val]
  change k.val%grid+grid*(k.val/grid%grid+grid*(k.val/grid/grid%grid))=k.val
  rw [Nat.mod_eq_of_lt hqq,Nat.mod_add_div,Nat.mod_add_div]

def pointEquiv (grid : ℕ) [NeZero grid] : Fin (grid^3)≃(Fin 3→ZMod grid) where
  toFun k := point grid k
  invFun j := ⟨pack grid j,pack_lt grid j⟩
  left_inv k := Fin.ext (pack_point grid k)
  right_inv := point_pack grid

theorem sum_point (grid : ℕ) [NeZero grid] (f : (Fin 3→ZMod grid)→ℚ) :
    (∑k:Fin (grid^3),f (point grid k))=∑j,f j :=
  (pointEquiv grid).sum_comp f

theorem phase_remainder (grid index : ℕ) [NeZero grid] (a : Fin 3→ZMod grid) :
    (∑i,(a i).val*digits grid index i)%grid=(∑i,a i*point grid index i).val := by
  rw [←ZMod.val_natCast]
  congr 1
  simp only [Nat.cast_sum,Nat.cast_mul,ZMod.natCast_zmod_val,point]

#print axioms pointEquiv
#print axioms sum_point
#print axioms phase_remainder
end Maxwell.Continuum.RationalDataflow.RootGrid
