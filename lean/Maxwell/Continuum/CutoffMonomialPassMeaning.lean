import Maxwell.Continuum.CutoffMonomialPassMachine
import Maxwell.Continuum.CutoffMonomialTableMeaning

/-! A completed charged traversal stores exactly the next shared polynomial
state, including its sentinel. No abstract row-update correctness is assumed. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem monomialPassTable_partial {D W : ℕ} (a b : Table (4*(D+1))) (coeff : ℕ→Parts)
    (hw : ∀j<D,(coeff j).Width W) (hc : ∀j,(coeff j).Valid) (j : ℕ) (hj : j<D)
    (h : MonomialStored a (monomialState D coeff j)) (v : ℕ→Parts)
    (hv : WidthBank (Finset.range 8) (monomialStorageWidth D W) v)
    (hg : Good (Finset.range 8) v) (h4 : v 4=coeff j) (h5 : v 5=Parts.literal 2)
    (hfit : monomialStorageWidth D W≤addressValue b.width) (k : ℕ) (hk : k≤D) :
    (monomialPassTable a b v k).getD 1=b.getD 1 ∧
    ∀r : Fin D,D-k≤r.val →
      (monomialPassTable a b v k).getD (4*r.val+4)=(monomialState D coeff (j+1)).older.get r ∧
      (monomialPassTable a b v k).getD (4*r.val+5)=(monomialState D coeff (j+1)).current.get r ∧
      (monomialPassTable a b v k).getD (4*r.val+6)=(monomialState D coeff (j+1)).total.get r := by
  induction k with
  | zero =>
    refine ⟨rfl,?_⟩
    intro r hr
    omega
  | succ k ih =>
    have hkd : k<D := by omega
    have hp := ih hkd.le
    have rowBound : D-1-k<D := by omega
    let row : Fin D := ⟨D-1-k,rowBound⟩
    have hstate := monomialPassState_invariant a coeff hw hc j hj h v hv hg h4 h5 k hkd.le
    have hnext := monomialPassState_invariant a coeff hw hc j hj h v hv hg h4 h5 (k+1) hk
    have fits : ∀i∈[1,6,7],(monomialRowState a row.val (monomialPassState a v k) i).Width
        (addressValue (monomialPassTable a b v k).width) := by
      intro i hi
      have his : i∈Finset.range 8 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        simp only [Finset.mem_range]
        omega
      have hb := (hnext.1 i his).mono hfit
      rw [monomialPassState_succ] at hb
      simpa only [(monomialPassTable_metadata a b v k).1] using hb
    refine ⟨?_,?_⟩
    · rw [monomialPassTable,monomialRowTable_sentinel]
      exact hp.1
    · intro r hr
      by_cases he : r=row
      · subst r
        exact monomialRowTable_next_row a (monomialPassTable a b v k) coeff j h row
          (monomialPassState a v k) hstate.2.2.1 hstate.2.2.2 fits
      · have hne : row≠r := Ne.symm he
        have hprev : D-k≤r.val := by
          have hvne : r.val≠D-1-k := by
            intro hv'
            exact he (Fin.ext hv')
          omega
        have prior := hp.2 r hprev
        change (monomialRowTable a (monomialPassTable a b v k) row.val (monomialPassState a v k)).getD _=_ ∧
          (monomialRowTable a (monomialPassTable a b v k) row.val (monomialPassState a v k)).getD _=_ ∧
          (monomialRowTable a (monomialPassTable a b v k) row.val (monomialPassState a v k)).getD _=_
        rw [monomialRowTable_other_row a _ row r hne _ 4 (by simp),
          monomialRowTable_other_row a _ row r hne _ 5 (by simp),
          monomialRowTable_other_row a _ row r hne _ 6 (by simp)]
        exact prior

theorem monomialPassTable_stored {D W : ℕ} (a b : Table (4*(D+1))) (coeff : ℕ→Parts)
    (hw : ∀j<D,(coeff j).Width W) (hc : ∀j,(coeff j).Valid) (j : ℕ) (hj : j<D)
    (h : MonomialStored a (monomialState D coeff j)) (v : ℕ→Parts)
    (hv : WidthBank (Finset.range 8) (monomialStorageWidth D W) v)
    (hg : Good (Finset.range 8) v) (h4 : v 4=coeff j) (h5 : v 5=Parts.literal 2)
    (hfit : monomialStorageWidth D W≤addressValue b.width) (hsentinel : b.getD 1=Parts.literal 0) :
    MonomialStored (monomialPassTable a b v D) (monomialState D coeff (j+1)) := by
  have hfinal := monomialPassTable_partial a b coeff hw hc j hj h v hv hg h4 h5 hfit D le_rfl
  exact ⟨hfinal.1.trans hsentinel,fun r => hfinal.2 r (by omega)⟩

#print axioms monomialPassTable_stored
end Maxwell.Continuum.Calibration.RawCutoff
