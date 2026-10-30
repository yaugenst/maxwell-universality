import Maxwell.Continuum.CutoffMonomialLayout
import Maxwell.Continuum.RationalDataflowRowFold

/-! The cached row traversal retains a polynomial raw-word width. The
bound is inferred from the actual Chebyshev recurrence, not a trace premise. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem monomialRowControl_keep (v : ℕ→Parts) (i : ℕ) (h6 : i≠6) (h7 : i≠7) :
    monomialRowControl.evaluate v i=v i := by
  simp only [monomialRowControl,Control.evaluate,Instruction.update,BinaryOp.eval,
    Function.update_of_ne h6,Function.update_of_ne h7]

theorem monomialRowState_keep {n : ℕ} (a : Table n) (r : ℕ) (v : ℕ→Parts)
    (i : ℕ) (hi : 4 ≤ i) (h6 : i≠6) (h7 : i≠7) : monomialRowState a r v i=v i := by
  rw [monomialRowState,monomialRowControl_keep _ i h6 h7,monomialLoaded_eq]
  simp only [Function.update_of_ne (by omega : i≠0),Function.update_of_ne (by omega : i≠1),
    Function.update_of_ne (by omega : i≠2),Function.update_of_ne (by omega : i≠3)]

theorem monomialRowState_width {D W : ℕ} (a : Table (4*(D+1))) (coeff : ℕ→Parts)
    (hw : ∀j<D,(coeff j).Width W) (j : ℕ) (hj : j<D)
    (h : MonomialStored a (monomialState D coeff j)) (r : Fin D) (v : ℕ→Parts)
    (hv : WidthBank (Finset.range 8) (monomialStorageWidth D W) v)
    (h4 : v 4=coeff j) (h5 : v 5=Parts.literal 2) :
    WidthBank (Finset.range 8) (monomialStorageWidth D W) (monomialRowState a r.val v) := by
  have hl := monomialLoaded_width a coeff hw j hj.le h r v hv
  have ho := monomialRowState_coordinates a coeff j h r v h4 h5
  have hn := monomialState_row_width D W coeff hw (j+1) hj r
  intro i hi
  by_cases h6 : i=6
  · subst i; rw [ho.2.1]; exact hn.2.1
  by_cases h7 : i=7
  · subst i; rw [ho.2.2]; exact hn.2.2
  rw [monomialRowState,monomialRowControl_keep _ i h6 h7]
  exact hl i hi

def monomialPassState {D : ℕ} (a : Table (4*(D+1))) (v : ℕ→Parts) : ℕ→(ℕ→Parts) :=
  rowIterate a 4 monomialReadPlan monomialRowControl D v

theorem monomialPassState_succ {D : ℕ} (a : Table (4*(D+1))) (v : ℕ→Parts) (k : ℕ) :
    monomialPassState a v (k+1)=monomialRowState a (D-1-k) (monomialPassState a v k) := rfl

theorem monomialPassState_invariant {D W : ℕ} (a : Table (4*(D+1))) (coeff : ℕ→Parts)
    (hw : ∀j<D,(coeff j).Width W) (hc : ∀j,(coeff j).Valid) (j : ℕ) (hj : j<D)
    (h : MonomialStored a (monomialState D coeff j)) (v : ℕ→Parts)
    (hv : WidthBank (Finset.range 8) (monomialStorageWidth D W) v)
    (hg : Good (Finset.range 8) v) (h4 : v 4=coeff j) (h5 : v 5=Parts.literal 2)
    (k : ℕ) (hk : k≤D) :
    WidthBank (Finset.range 8) (monomialStorageWidth D W) (monomialPassState a v k) ∧
    Good (Finset.range 8) (monomialPassState a v k) ∧
    monomialPassState a v k 4=coeff j ∧ monomialPassState a v k 5=Parts.literal 2 := by
  induction k with
  | zero => exact ⟨hv,hg,h4,h5⟩
  | succ k ih =>
    have hkd : k<D := by omega
    have hp := ih hkd.le
    rw [monomialPassState_succ]
    have hr : D-1-k<D := by omega
    refine ⟨monomialRowState_width a coeff hw j hj h ⟨D-1-k,hr⟩ _ hp.1 hp.2.2.1 hp.2.2.2,?_,?_,?_⟩
    · exact monomialRowControl.evaluate_good (Finset.range 8) monomialRowControl_valid _
        (monomialLoaded_good a coeff hc j h ⟨D-1-k,hr⟩ _ hp.2.1)
        (monomialRowControl_admissible _)
    · rw [monomialRowState_keep _ _ _ 4 (by decide) (by decide) (by decide)]
      exact hp.2.2.1
    · rw [monomialRowState_keep _ _ _ 5 (by decide) (by decide) (by decide)]
      exact hp.2.2.2

def monomialWorkingWidth (D W : ℕ) : ℕ := 16*(monomialStorageWidth D W+1)

theorem monomialPassState_trace {D W : ℕ} (a : Table (4*(D+1))) (coeff : ℕ→Parts)
    (hw : ∀j<D,(coeff j).Width W) (hc : ∀j,(coeff j).Valid) (j : ℕ) (hj : j<D)
    (h : MonomialStored a (monomialState D coeff j)) (v : ℕ→Parts)
    (hv : WidthBank (Finset.range 8) (monomialStorageWidth D W) v)
    (hg : Good (Finset.range 8) v) (h4 : v 4=coeff j) (h5 : v 5=Parts.literal 2)
    (k : ℕ) (hk : k<D) :
    monomialRowControl.WidthTrace (Finset.range 8) (monomialWorkingWidth D W)
      (monomialLoaded a (D-1-k) (monomialPassState a v k)) := by
  have hp := monomialPassState_invariant a coeff hw hc j hj h v hv hg h4 h5 k hk.le
  exact monomialRowControl_widthTrace _ _
    (monomialLoaded_width a coeff hw j hj.le h ⟨D-1-k,by omega⟩ _ hp.1)

#print axioms monomialPassState_trace
end Maxwell.Continuum.Calibration.RawCutoff
