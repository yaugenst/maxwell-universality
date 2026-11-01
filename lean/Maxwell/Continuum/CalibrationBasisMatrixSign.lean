import Maxwell.Continuum.CalibrationBasisColumnFrame
import Maxwell.Continuum.CalibrationSymmetricSignAdapter

/-! The actual24-column Schur construction feeds the actual symmetrized
sign circuit. Fresh and repeated calls share the same isolated central bank. -/
namespace Maxwell.Continuum.Calibration.BasisMatrixSign
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow CentralRelocation
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount
  CentralRelocation.bank count gap relocation MatrixInverse.tapeBound MatrixInverse.registers
  PolynomialExpression.determinantNodes SymmetricSign.width SymmetricSign.result

def code : Code := .seq BasisMatrix.fullCode EdgeSignRelocation.code

theorem input_subset : inputRegisters⊆SchurRow.bank := by
  intro i hi
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)

theorem input_width {R heap P : ℕ} {p : ℕ→Parts} {s : Store}
    (state : BasisColumn.State R heap P p s) : WidthBank inputRegisters (max 2 P) p :=
  fun i hi=>(state.schur_width i (input_subset hi)).mono (le_max_right _ _)

theorem original_scratch (v : ℕ→Parts) (s : Store)
    (ready : Ready bank v (s.renameTapes relocation)) : NatAssign.Scratch s.val := by
  intro i hi
  apply RationalAccumulator.blank_of_eq ?_ (ready.2 i hi)
  exact ((state_tape s i).trans (congrArg s.val.tapes (scratch_fixed i hi))).symm

theorem state_retained {R heap P : ℕ} {p v : ℕ→Parts} {s t : Store}
    (state : BasisColumn.State R heap P p s) (frame : BinaryPrecision.Frame work s.val t.val)
    (ready : Ready bank v (t.renameTapes relocation)) : BasisColumn.State R heap P p t :=
  state.transfer (fun k lo hi=>retained frame k lo (by unfold count;omega)) (original_scratch v t ready)

theorem central_retained (v : ℕ→Parts) (s t : Store)
    (ready : Ready bank v (s.renameTapes relocation))
    (high : ∀k,gap≤k→t.val.tapes k=s.val.tapes k) (scratch : NatAssign.Scratch t.val) :
    Ready bank v (t.renameTapes relocation) := by
  refine ⟨?_,?_⟩
  · intro i hi
    apply RationalAccumulator.word_of_eq ?_ (ready.1 i hi)
    rw [state_tape,state_tape,moved i (ids_ge _ _ hi) (bank_bound i hi)]
    exact high _ (by omega)
  · intro i hi
    exact RationalAccumulator.blank_of_eq
      ((state_tape t i).trans (congrArg t.val.tapes (scratch_fixed i hi))) (scratch i hi)

theorem executes (R heap P : ℕ) (p : ℕ→Parts) (radius : 3≤R)
    (physical : BasisColumn.admissible p) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : BasisColumn.State R heap P p s) (fresh : ∀i,gap≤ i→RationalAccumulator.Blank s.val i) :
    ∃cost t out Q,Executes input tape code cost s t ∧ BasisColumn.State R heap Q out t ∧
      t.val.registers 31=negativeTest (symmetricRationalMatrix (BasisColumn.matrix R p)) ∧
      (∀row column,(out (SchurRow.output row column)).value=BasisColumn.matrix R p row column) ∧
      (∀i,i<240→ out i=p i) ∧
      Ready bank (EdgeSignRelocation.result out) (t.renameTapes relocation) ∧
      Good bank (EdgeSignRelocation.result out) ∧
      WidthBank bank (SymmetricSign.width (max 2 Q)) (EdgeSignRelocation.result out) ∧
      (∀k,6000≤k→k<count→t.val.tapes k=s.val.tapes k) ∧
      (∀k,850≤k→k<924→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,out,Q,e0,state0,values,keep,high,interval⟩:=
    BasisMatrix.full_executes R heap P p radius physical input tape s state
  have matrix : EdgeSignRelocation.matrix out=BasisColumn.matrix R p := by
    funext i j
    exact values i j
  have fresh0 : ∀i,gap≤ i→RationalAccumulator.Blank u.val i := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (high i (by unfold gap count at hi;omega)) (fresh i hi)
  obtain ⟨c1,t,e1,_,decision,central,good,width,frame⟩:=EdgeSignRelocation.executes out (max 2 Q)
    (le_max_left _ _) (input_width state0) (fun i hi=>state0.schur_good i (input_subset hi))
    input tape u (fun i hi=>state0.schur_cells i (input_subset hi)) fresh0 state0.ready.parts.2
  exact ⟨c0+c1,t,out,Q,e0.seq e1,state_retained state0 frame central,by simpa only [matrix] using decision,
    values,keep,central,good,width,fun k lo hi=>(retained frame k (by omega) hi).trans (high k lo),
    fun k lo hi=>(retained frame k (by omega) (by unfold count;omega)).trans (interval k lo hi)⟩

theorem reexecutes (R heap P W : ℕ) (p old : ℕ→Parts) (radius : 3≤R) (positive : 1≤W)
    (physical : BasisColumn.admissible p) (oldWidth : WidthBank bank W old)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : BasisColumn.State R heap P p s)
    (oldReady : Ready bank old (s.renameTapes relocation)) :
    ∃cost t out Q,Executes input tape code cost s t ∧ BasisColumn.State R heap Q out t ∧
      t.val.registers 31=negativeTest (symmetricRationalMatrix (BasisColumn.matrix R p)) ∧
      (∀row column,(out (SchurRow.output row column)).value=BasisColumn.matrix R p row column) ∧
      (∀i,i<240→ out i=p i) ∧
      Ready bank (EdgeSignRelocation.result out) (t.renameTapes relocation) ∧
      Good bank (EdgeSignRelocation.result out) ∧
      WidthBank bank (SymmetricSign.width (max 2 Q)) (EdgeSignRelocation.result out) ∧
      (∀k,6000≤k→k<count→t.val.tapes k=s.val.tapes k) ∧
      (∀k,850≤k→k<924→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,out,Q,e0,state0,values,keep,high,interval⟩:=
    BasisMatrix.full_executes R heap P p radius physical input tape s state
  have matrix : EdgeSignRelocation.matrix out=BasisColumn.matrix R p := by
    funext i j
    exact values i j
  have ready0:=central_retained old s u oldReady (fun k hk=>high k (by unfold gap count at hk;omega)) state0.ready.parts.2
  obtain ⟨c1,t,e1,_,decision,central,good,width,frame⟩:=EdgeSignRelocation.reexecutes out old (max 2 Q) W
    (le_max_left _ _) positive (input_width state0) (fun i hi=>state0.schur_good i (input_subset hi)) oldWidth
    input tape u (fun i hi=>state0.schur_cells i (input_subset hi)) ready0
  exact ⟨c0+c1,t,out,Q,e0.seq e1,state_retained state0 frame central,by simpa only [matrix] using decision,
    values,keep,central,good,width,fun k lo hi=>(retained frame k (by omega) hi).trans (high k lo),
    fun k lo hi=>(retained frame k (by omega) (by unfold count;omega)).trans (interval k lo hi)⟩

#print axioms executes
#print axioms reexecutes
end Maxwell.Continuum.Calibration.BasisMatrixSign
