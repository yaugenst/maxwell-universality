import Maxwell.Continuum.CalibrationRootGridCleanup

/-! Literal runtime decoding of a coefficient index. An odd product grid
enumerates the centered Fourier cube; modular negative frequencies are
computed with multiplication and quotient/remainder, without signed division. -/
namespace Maxwell.Continuum.RationalDataflow.RootFrequency
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.ArrayDecodeMachine (divModValues divModValues_width nat_values_width)
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def ids : Finset ℕ := NaturalQuotient.workPorts∪Finset.Icc 330 344
def prepare : List NatAssign.Instruction := [.literal 343 2,.literal 344 1]
def prepared (n : ℕ→ℕ) := NatAssign.values prepare n
def pair (n : ℕ→ℕ) := divModValues (prepared n) 330 343 330 341
def coordinateFirst (n : ℕ→ℕ) := divModValues (pair n) 330 331 332 333
def coordinateSecond (n : ℕ→ℕ) := divModValues (coordinateFirst n) 332 331 332 334
def coordinates (n : ℕ→ℕ) := divModValues (coordinateSecond n) 332 331 340 335
def halved (n : ℕ→ℕ) := divModValues (coordinates n) 331 343 339 340
def factor : List NatAssign.Instruction := [.copy 339 340,.multiply 343 340]
def factored (n : ℕ→ℕ) := NatAssign.values factor (halved n)
def negativePrepare (coordinate : ℕ) : List NatAssign.Instruction :=
  [.copy coordinate 341,.multiply 340 341,.add 339 341]
def negative (coordinate target : ℕ) (n : ℕ→ℕ) :=
  divModValues (NatAssign.values (negativePrepare coordinate) n) 341 331 332 target
def values (n : ℕ→ℕ) := negative 335 338 (negative 334 337 (negative 333 336 (factored n)))

def frequency (grid index : ℕ) : Fin 3→ℤ :=
  fun i => (RootGrid.digits grid (index/2) i:ℤ)-((grid/2:ℕ):ℤ)

theorem pair_values (n : ℕ→ℕ) : pair n 330=n 330/2 ∧ pair n 341=n 330%2 ∧
    pair n 331=n 331 ∧ pair n 343=2 ∧ pair n 344=1 := by
  simp [pair,prepared,prepare,divModValues,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem values_coordinates (n : ℕ→ℕ) (i : Fin 3) :
    ![values n 336,values n 337,values n 338] i=
      (2*(n 331/2)*RootGrid.digits (n 331) (n 330/2) i+n 331/2)%(n 331) := by
  fin_cases i <;>
    simp [values,negative,negativePrepare,factored,factor,halved,coordinates,coordinateSecond,
      coordinateFirst,pair,prepared,prepare,divModValues,RootGrid.digits,
      NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      Nat.add_comm,Nat.mul_comm]

theorem modular_negative (grid degree digit : ℕ) [NeZero grid] (hgrid : grid=2*degree+1) :
    ((2*degree*digit+degree)%grid)=
      ((-((digit:ℤ)-(degree:ℤ)):ℤ):ZMod grid).val := by
  rw [← ZMod.val_natCast]
  congr 1
  have hz : (grid:ZMod grid)=0 := ZMod.natCast_self grid
  have hm : 2*(degree:ZMod grid)=-1 := by
    have hc : ((2*degree+1:ℕ):ZMod grid)=0 := by rw [←hgrid];exact hz
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hc
    exact eq_neg_of_add_eq_zero_left hc
  push_cast
  rw [hm]
  ring

theorem values_frequency (n : ℕ→ℕ) (grid degree : ℕ) [NeZero grid]
    (hn : n 331=grid) (hgrid : grid=2*degree+1) (i : Fin 3) :
    ![values n 336,values n 337,values n 338] i=
      ((-(PeriodicSampling.Product.frequency grid (frequency grid (n 330)))) i).val := by
  rw [values_coordinates,hn]
  have hd : grid/2=degree := by omega
  simp only [PeriodicSampling.Product.frequency,Pi.neg_apply,frequency]
  rw [hd]
  simpa only [Int.cast_neg] using modular_negative grid degree (RootGrid.digits grid (n 330/2) i) hgrid

theorem negative_keep (coordinate target : ℕ) (n : ℕ→ℕ) (i : ℕ)
    (h341 : i≠341) (h332 : i≠332) (htarget : i≠target) : negative coordinate target n i=n i := by
  simp only [negative,negativePrepare,divModValues,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,Function.update_of_ne h341,Function.update_of_ne h332,
    Function.update_of_ne htarget]

theorem values_keep (n : ℕ→ℕ) (i : ℕ)
    (hi : i∈NaturalQuotient.workPorts ∨ i=331 ∨ 344 < i) : values n i=n i := by
  have hh := hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
  rw [values,negative_keep _ _ _ i (by omega) (by omega) (by omega),
    negative_keep _ _ _ i (by omega) (by omega) (by omega),
    negative_keep _ _ _ i (by omega) (by omega) (by omega)]
  simp only [factored,factor,halved,coordinates,coordinateSecond,coordinateFirst,pair,prepared,prepare,
    divModValues,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    Function.update_of_ne (by omega : i≠340),Function.update_of_ne (by omega : i≠339),
    Function.update_of_ne (by omega : i≠335),Function.update_of_ne (by omega : i≠334),
    Function.update_of_ne (by omega : i≠333),Function.update_of_ne (by omega : i≠332),
    Function.update_of_ne (by omega : i≠330),Function.update_of_ne (by omega : i≠341),
    Function.update_of_ne (by omega : i≠343),Function.update_of_ne (by omega : i≠344)]

theorem negative_values (coordinate target : ℕ) (n : ℕ→ℕ) :
    negative coordinate target n target=(n 340*n coordinate+n 339)%(n 331) := by
  simp [negative,negativePrepare,divModValues,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Nat.add_comm]

#print axioms values_frequency
end Maxwell.Continuum.RationalDataflow.RootFrequency
