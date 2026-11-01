import Maxwell.Continuum.CalibrationEdgeBisectionLoop

/-! Initialize the concrete edge loop from the computed precision word.
The bracket and isolated central bank are actually written before any test. -/
namespace Maxwell.Continuum.Calibration.EdgeBisection
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow CentralRelocation
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] CentralRelocation.bank count gap relocation
  MatrixInverse.tapeBound MatrixInverse.registers PolynomialExpression.determinantNodes
  SymmetricSign.width SymmetricSign.result BasisForcing.bank SchurRow.nodeCount edgeInitial

def initializeCode : Code := .seq EdgeController.initializeCode
  (.seq EdgeBracketMachine.initializeCode CentralRelocation.initializeCode)
def code : Code := .seq initializeCode finishCode

theorem initialize_executes (target heap R P C : ℕ) (p : ℕ → Parts) (v : ℕ → ℕ)
    (selected : v 4418=target) (width : ∀i∈EdgeController.ids,(v i).bits.length ≤ C)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (state : BasisColumn.State R heap P p s)
    (controller : NatAssign.Bank EdgeController.ids v s.val)
    (machin : EdgeScalar.RelocatedFresh s.val)
    (bracket : ∀i∈SignedBracket.ids EdgeBracketMachine.base,RationalAccumulator.Blank s.val i)
    (central : ∀i,gap ≤ i → RationalAccumulator.Blank s.val i) :
    ∃cost t d,Executes input tape initializeCode cost s t ∧ Ready target heap 0 d t ∧
      (∀i,860 ≤ i → i<900 → t.val.tapes i=s.val.tapes i) := by
  obtain ⟨c0,s0,e0,_,control0,scratch0,width0,_,_,radius0,frame0⟩:=
    EdgeController.initialize_executes v C width input tape s controller state.ready.parts.2
  have basis0:=state.rebase frame0 scratch0 radius0
  have bracket0 : ∀i∈SignedBracket.ids EdgeBracketMachine.base,RationalAccumulator.Blank s0.val i := by
    intro i hi
    have bounds:=bracket_bounds i hi
    exact RationalAccumulator.blank_of_eq
      (frame0.tapes i (controller_outside i (by omega) (by omega) (Or.inr (by omega)))) (bracket i hi)
  have central0 : ∀i,gap ≤ i → RationalAccumulator.Blank s0.val i := by
    intro i hi
    have low : 10000 ≤ i := by unfold gap count at hi;omega
    exact RationalAccumulator.blank_of_eq
      (frame0.tapes i (controller_outside i (by omega) (by omega) (Or.inr (by omega)))) (central i hi)
  obtain ⟨c1,s1,e1,_,bracket1,scratch1,width1,frame1⟩:=
    EdgeBracketMachine.initialize_executes input tape s0 bracket0 scratch0
  have basis1:=bracket_basis basis0 frame1 scratch1
  have control1:=bracket_controller
    (fun i hi=>control0 i (Finset.mem_insert_of_mem hi)) frame1
  have machin1:=bracket_machin (controller_machin machin frame0) frame1
  have central1 : ∀i,gap ≤ i → RationalAccumulator.Blank s1.val i := by
    intro i hi
    exact RationalAccumulator.blank_of_eq
      (frame1.tapes i (bracket_outside i (by unfold gap count at hi;omega)
        (Or.inr (by unfold gap count at hi;omega)))) (central0 i hi)
  obtain ⟨c2,t,e2,_,ready2,frame2⟩:=CentralRelocation.initialize_executes input tape s1 central1 scratch1
  have keep (i : ℕ) (lo : 4 ≤ i) (hi : i<10000) : t.val.tapes i=s1.val.tapes i :=
    retained frame2 i lo (by unfold count;omega)
  let d : Data :=
    { scalar:=p
      bracket:=EdgeBracketMachine.initial edgeInitial
      control:=EdgeController.initialValues v
      central:=Initialize.parts
      scalarWidth:=P
      bracketWidth:=EdgeBracketMachine.initialWidth
      controlWidth:=EdgeController.initialWidth C
      centralWidth:=1 }
  have finished : Ready target heap 0 d t := by
    have fields:=EdgeController.initial_fields v
    refine ⟨BasisMatrixSign.state_retained basis1 frame2 ready2,?_,width1,?_,
      EdgeBracketMachine.initial_represents,?_,?_,?_,?_,?_,by omega,?_,ready2,Initialize.width bank,Nat.le_refl 1⟩
    · intro i hi
      have bounds:=bracket_bounds i hi
      exact RationalAccumulator.word_of_eq (keep i (by omega) (by omega)) (bracket1 i hi)
    · change 7 ≤ EdgeBracketMachine.initialWidth
      norm_num [EdgeBracketMachine.initialWidth]
    · intro i hi
      have bounds:=controller_bounds i hi
      exact RationalAccumulator.word_of_eq (keep i (by omega) (by omega)) (control1 i hi)
    · exact fun i hi=>width0 i (Finset.mem_insert_of_mem hi)
    · exact fields.1
    · simpa only [d,selected,Nat.sub_zero] using fields.2.1
    · exact fields.2.2.2.1
    · intro i lo hi
      exact RationalAccumulator.blank_of_eq (keep i (by omega) (by omega)) (machin1 i lo hi)
  refine ⟨c0+(c1+c2),t,d,e0.seq (e1.seq e2),finished,?_⟩
  intro i lo hi
  exact (keep i (by omega) (by omega)).trans
    ((frame1.tapes i (bracket_outside i (by omega) (Or.inl (by omega)))).trans
      (frame0.tapes i (controller_outside i (by omega) (by omega) (Or.inr lo))))

theorem executes (target heap R P C : ℕ) (p : ℕ → Parts) (v : ℕ → ℕ)
    (selected : v 4418=target) (width : ∀i∈EdgeController.ids,(v i).bits.length ≤ C)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (state : BasisColumn.State R heap P p s)
    (controller : NatAssign.Bank EdgeController.ids v s.val)
    (machin : EdgeScalar.RelocatedFresh s.val)
    (bracket : ∀i∈SignedBracket.ids EdgeBracketMachine.base,RationalAccumulator.Blank s.val i)
    (central : ∀i,gap ≤ i → RationalAccumulator.Blank s.val i) :
    ∃cost t d mid,Executes input tape code cost s t ∧ Ready target heap (2*target) d t ∧
      StoredParts.Stored (positivePort 2302) mid t.val ∧ 0<mid.denominator ∧
      mid.Width d.bracketWidth ∧ mid.value=(calibratedEdge target).center ∧
      (∀i,860 ≤ i → i<900 → t.val.tapes i=s.val.tapes i) := by
  obtain ⟨c0,u,d,e0,ready,keep0⟩:=initialize_executes target heap R P C p v selected width input tape s
    state controller machin bracket central
  obtain ⟨c1,t,out,mid,e1,finished,stored,positive,words,meaning,keep1⟩:=finish_executes target heap d input tape u ready
  exact ⟨c0+c1,t,out,mid,e0.seq e1,finished,stored,positive,words,meaning,
    fun i lo hi=>(keep1 i lo hi).trans (keep0 i lo hi)⟩

#print axioms initialize_executes
#print axioms executes
end Maxwell.Continuum.Calibration.EdgeBisection
