import Maxwell.Continuum.CutoffMonomialSeedMachine
import Maxwell.Continuum.CutoffMonomialCoefficientLoad
import Maxwell.Continuum.RationalDataflowLaneCopyRows
import Maxwell.Continuum.ProfileTableState

/-! Exact initialization from a stored coefficient lane. The source can be
an encoded profile or the first initialized cache buffer. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def loadedMonomialTable {n D : ℕ} (a : Table n) (b : Table (4*(D+1)))
    (stride offset : ℕ) : Table (4*(D+1)) :=
  laneCopyRowsTable a (monomialSeedTable b) D stride offset 4 7 D

def loadedMonomialValues {n : ℕ} (a : Table n) (D stride offset : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  laneCopyRowsValues a D stride offset 1 (Function.update v 0 (Parts.literal 1)) D

theorem monomialSeedTable_metadata {D : ℕ} (b : Table (4*(D+1))) :
    Profile.Runtime.tableMetadata b (monomialSeedTable b) := by
  unfold Profile.Runtime.tableMetadata monomialSeedTable Table.setD
  split_ifs <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem loadedMonomialTable_metadata {n D : ℕ} (a : Table n) (b : Table (4*(D+1)))
    (stride offset : ℕ) : Profile.Runtime.tableMetadata b (loadedMonomialTable a b stride offset) := by
  have h := laneCopyRowsTable_metadata a (monomialSeedTable b) D stride offset 4 7 D
  have g := monomialSeedTable_metadata b
  exact ⟨h.1.trans g.1,h.2.1.trans g.2.1,h.2.2.1.trans g.2.2.1,
    h.2.2.2.1.trans g.2.2.2.1,h.2.2.2.2.trans g.2.2.2.2⟩

theorem laneCopyRows_other {n m : ℕ} (a : Table n) (b : Table m)
    (D srcStride srcOffset stride offset k i : ℕ) (hi : ∀r,stride*r+offset≠i) :
    (laneCopyRowsTable a b D srcStride srcOffset stride offset k).getD i=b.getD i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [laneCopyRowsTable,Table.setD_getD_ne _ _ _ _ (hi _)]
    exact ih

theorem laneCopyRows_stored {n D : ℕ} (a : Table n) (b : Table (4*(D+1)))
    (x : MonomialState D) (h : MonomialStored b x) (stride offset k : ℕ) :
    MonomialStored (laneCopyRowsTable a b D stride offset 4 7 k) x := by
  refine ⟨?_,?_⟩
  · exact (laneCopyRows_other a b D stride offset 4 7 k 1 (by intro r;omega)).trans h.1
  · intro r
    refine ⟨?_,?_,?_⟩
    · exact (laneCopyRows_other a b D stride offset 4 7 k (4*r.val+4) (by intro s;omega)).trans (h.2 r).1
    · exact (laneCopyRows_other a b D stride offset 4 7 k (4*r.val+5) (by intro s;omega)).trans (h.2 r).2.1
    · exact (laneCopyRows_other a b D stride offset 4 7 k (4*r.val+6) (by intro s;omega)).trans (h.2 r).2.2

theorem laneCopyRows_coefficients_partial {n D : ℕ} (a : Table n) (b : Table (4*(D+1)))
    (stride offset : ℕ)
    (hfit : ∀r : Fin D,(a.getD (stride*r.val+offset)).Width (addressValue b.width))
    (k : ℕ) (hk : k≤D) :
    ∀r : Fin D,D-k≤r.val →
      (laneCopyRowsTable a b D stride offset 4 7 k).getD (4*r.val+7)=a.getD (stride*r.val+offset) := by
  induction k with
  | zero => intro r hr;omega
  | succ k ih =>
    intro r hr
    have hkd : k<D := by omega
    have hrow : D-1-k<D := by omega
    by_cases he : r.val=D-1-k
    · rw [laneCopyRowsTable,he]
      apply Table.setD_getD_eq _ _ (by omega)
      simpa only [(laneCopyRowsTable_metadata a b D stride offset 4 7 k).1] using hfit ⟨D-1-k,hrow⟩
    · rw [laneCopyRowsTable,Table.setD_getD_ne _ _ _ _ (by omega)]
      exact ih hkd.le r (by omega)

theorem loadedMonomialTable_correct {n D : ℕ} (a : Table n) (b : Table (4*(D+1)))
    (stride offset : ℕ) (hD : 2≤D) (hwidth : 1≤addressValue b.width)
    (hfit : ∀r : Fin D,(a.getD (stride*r.val+offset)).Width (addressValue b.width))
    (coeff : ℕ→Parts) (hcoeff : ∀r<D,a.getD (stride*r+offset)=coeff r) :
    MonomialStored (loadedMonomialTable a b stride offset) (monomialState D coeff 0) ∧
    MonomialCoefficientsStored (loadedMonomialTable a b stride offset) coeff := by
  refine ⟨laneCopyRows_stored a (monomialSeedTable b) _
    (monomialSeedTable_stored b hD hwidth coeff) stride offset D,?_⟩
  intro r
  exact (laneCopyRows_coefficients_partial a (monomialSeedTable b) stride offset
    (by simpa only [(monomialSeedTable_metadata b).1] using hfit) D le_rfl r (by omega)).trans (hcoeff r.val r.isLt)

theorem laneCopyRowsValues_width {n : ℕ} (a : Table n) (D stride offset entry B : ℕ)
    (S : Finset ℕ) (v : ℕ→Parts) (hv : WidthBank S B v)
    (hw : ∀r<D,(a.getD (stride*r+offset)).Width B) (k : ℕ) (hk : k≤D) :
    WidthBank S B (laneCopyRowsValues a D stride offset entry v k) := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    exact (ih (by omega)).update entry (hw (D-1-k) (by omega))

theorem laneCopyRowsValues_good {n : ℕ} (a : Table n) (D stride offset entry : ℕ)
    (S : Finset ℕ) (v : ℕ→Parts) (hv : Good S v)
    (hg : ∀r<D,(a.getD (stride*r+offset)).Valid) (k : ℕ) (hk : k≤D) :
    Good S (laneCopyRowsValues a D stride offset entry v k) := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    exact (ih (by omega)).update entry (hg (D-1-k) (by omega))

theorem laneCopyRowsValues_other {n : ℕ} (a : Table n) (D stride offset entry : ℕ)
    (v : ℕ→Parts) (k i : ℕ) (hi : i≠entry) :
    laneCopyRowsValues a D stride offset entry v k i=v i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [laneCopyRowsValues,Function.update_of_ne hi,ih]

theorem loadedMonomialValues_bounds {n : ℕ} (a : Table n) (D stride offset B : ℕ)
    (S : Finset ℕ) (v : ℕ→Parts) (hB : 1≤B) (hv : WidthBank S B v) (hg : Good S v)
    (hw : ∀r<D,(a.getD (stride*r+offset)).Width B)
    (ha : ∀r<D,(a.getD (stride*r+offset)).Valid) :
    WidthBank S B (loadedMonomialValues a D stride offset v) ∧
    Good S (loadedMonomialValues a D stride offset v) ∧
    loadedMonomialValues a D stride offset v 5=v 5 := by
  refine ⟨laneCopyRowsValues_width a D stride offset 1 B S _
    (hv.update 0 ((Parts.literal_width RationalWords.width_one).mono hB)) hw D le_rfl,
    laneCopyRowsValues_good a D stride offset 1 S _
      (hg.update 0 (Parts.literal_valid 1)) ha D le_rfl,?_⟩
  exact (laneCopyRowsValues_other a D stride offset 1 _ D 5 (by decide)).trans
    (Function.update_of_ne (by decide) _ _)

#print axioms loadedMonomialTable_correct
#print axioms loadedMonomialValues_bounds
end Maxwell.Continuum.Calibration.RawCutoff
