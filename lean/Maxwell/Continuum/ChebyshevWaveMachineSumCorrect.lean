import Maxwell.Continuum.ChebyshevWaveMachineSumData

/-! The actual finite accumulation computes both rational Fourier centers. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem sumValues_input (Q P grid : ℕ) (q : ℚ) (n : ℤ) (v : ℕ→Parts)
    (hv : Good ids v) (hi : SumInput grid q n 0 v) (k : ℕ) :
    SumInput grid q n k (sumValues Q P v k) := by
  induction k with
  | zero => exact hi
  | succ k ih => exact sumStep_input Q P grid q n k _ (sumValues_good Q P v hv k) ih

theorem sumValues_values (grid : ℕ) [NeZero grid] (q : ℚ) (n : ℤ) (Q P : ℕ)
    (v : ℕ→Parts) (hv : Good ids v) (hi : SumInput grid q n 0 v)
    (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) (k : ℕ) (hk : k≤grid) :
    (sumValues Q P v k 8).value=∑j∈Finset.range k,(waveProductSample grid q Q P n (j:ZMod grid)).re.center ∧
    (sumValues Q P v k 9).value=∑j∈Finset.range k,(waveProductSample grid q Q P n (j:ZMod grid)).im.center := by
  induction k with
  | zero => simpa only [sumValues,Finset.range_zero,Finset.sum_empty] using And.intro hz0 hz1
  | succ k ih =>
    have old := ih (by omega)
    have next := sumStep_values grid q n Q P k _ (sumValues_good Q P v hv k)
      (sumValues_input Q P grid q n v hv hi k) (by omega)
    simpa only [sumValues,old.1,old.2,Finset.sum_range_succ] using next

theorem sum_range_zmod (grid : ℕ) [NeZero grid] (f : ZMod grid→ℚ) :
    ∑j∈Finset.range grid,f (j:ZMod grid)=∑j:ZMod grid,f j := by
  refine Finset.sum_bij (fun j _ => (j:ZMod grid)) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj he
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (Finset.mem_range.mp hi),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] using hv
  · intro j _
    exact ⟨j.val,Finset.mem_range.mpr (ZMod.val_lt j),ZMod.natCast_zmod_val j⟩

def normalizeInstructions : List RationalDataflow.Instruction :=
  [.binary .mul 8 11 8,.binary .mul 9 11 9]
def coefficientValues (Q P grid : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  evaluate normalizeInstructions (sumValues Q P v grid)

theorem coefficientValues_correct (grid : ℕ) [NeZero grid] (q : ℚ) (n : ℤ) (Q P : ℕ)
    (v : ℕ→Parts) (hv : Good ids v) (hi : SumInput grid q n 0 v)
    (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) :
    (coefficientValues Q P grid v 8).value=(rationalWaveCoefficient grid q Q P n).re.center ∧
    (coefficientValues Q P grid v 9).value=(rationalWaveCoefficient grid q Q P n).im.center := by
  have hs := sumValues_values grid q n Q P v hv hi hz0 hz1 grid le_rfl
  have hr := (sumValues_input Q P grid q n v hv hi grid).reciprocal
  simp only [coefficientValues,normalizeInstructions,evaluate,RationalDataflow.Instruction.update,
    BinaryOp.eval,Function.update_self,Function.update_of_ne (by decide : (8:ℕ)≠9),
    Function.update_of_ne (by decide : (9:ℕ)≠8),Function.update_of_ne (by decide : (11:ℕ)≠8),
    Parts.mul_value,hr,hs.1,hs.2,rationalWaveCoefficient,
    Maxwell.Certificate.ComplexRectangle.point]
  exact ⟨congrArg (fun x : ℚ => (grid:ℚ)⁻¹*x)
    (sum_range_zmod grid (fun j => (waveProductSample grid q Q P n j).re.center)),
    congrArg (fun x : ℚ => (grid:ℚ)⁻¹*x)
    (sum_range_zmod grid (fun j => (waveProductSample grid q Q P n j).im.center))⟩

#print axioms coefficientValues_correct
end Maxwell.Continuum.Profile.WaveMachine
