import Maxwell.Continuum.CutoffMonomialTableMeaning
import Maxwell.Continuum.RationalDataflowArrayFill

/-! Exact initial cached rows: a fully written zero table, then the two
unit coefficients of T0 and T1. No preinitialized memory is presumed. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def monomialSeedTable {D : ℕ} (b : Table (4*(D+1))) : Table (4*(D+1)) :=
  ((b.filled (fun _ => Parts.literal 0) 0).setD 4 (Parts.literal 1)).setD 9 (Parts.literal 1)

theorem zeroTable_getD {n : ℕ} (b : Table n) (hwidth : 1≤addressValue b.width)
    (i : ℕ) (hi : i<n) : (b.filled (fun _ => Parts.literal 0) 0).getD i=Parts.literal 0 := by
  simp only [Table.getD,dite_eq_left hi]
  exact b.filled_get _ (fun _ => (Parts.literal_width RationalWords.width_zero').mono hwidth) ⟨i,hi⟩

theorem monomialSeedTable_stored {D : ℕ} (b : Table (4*(D+1))) (hD : 2≤D)
    (hwidth : 1≤addressValue b.width) (coeff : ℕ→Parts) :
    MonomialStored (monomialSeedTable b) (monomialState D coeff 0) := by
  have h1 : (Parts.literal 1).Width (addressValue b.width) :=
    (Parts.literal_width RationalWords.width_one).mono hwidth
  have h4 : 4<4*(D+1) := by omega
  have h9 : 9<4*(D+1) := by omega
  constructor
  · unfold monomialSeedTable
    rw [Table.setD_getD_ne _ _ _ _ (by decide),Table.setD_getD_ne _ _ _ _ (by decide)]
    exact zeroTable_getD b hwidth 1 (by omega)
  · intro r
    simp only [monomialState,rawChebyshevState,vector_get_ofFn]
    refine ⟨?_,?_,?_⟩
    · unfold monomialSeedTable
      rw [Table.setD_getD_ne _ _ _ _ (by omega)]
      by_cases hr : r.val=0
      · simp only [hr,Nat.mul_zero,Nat.zero_add,ite_true]
        apply Table.setD_getD_eq _ _ h4
        exact h1
      · rw [Table.setD_getD_ne _ _ _ _ (by omega),ite_eq_right hr]
        exact zeroTable_getD b hwidth _ (by omega)
    · unfold monomialSeedTable
      by_cases hr : r.val=1
      · simp only [hr,ite_true]
        apply Table.setD_getD_eq _ _ h9
        simpa only [Table.setD_width,Table.filled] using h1
      · rw [Table.setD_getD_ne _ _ _ _ (by omega),Table.setD_getD_ne _ _ _ _ (by omega),ite_eq_right hr]
        exact zeroTable_getD b hwidth _ (by omega)
    · unfold monomialSeedTable
      rw [Table.setD_getD_ne _ _ _ _ (by omega),Table.setD_getD_ne _ _ _ _ (by omega)]
      exact zeroTable_getD b hwidth _ (by omega)

#print axioms monomialSeedTable_stored
end Maxwell.Continuum.Calibration.RawCutoff
