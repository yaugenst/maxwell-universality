import Maxwell.Continuum.FourierTensorDirectFrame
import Maxwell.Continuum.RationalDataflowNaturalChannels

/-! Fixed increment of the actual tensor cursor. Only its natural index
channel is used; the actual bounded index proves the reusable word width. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def cursorCode (i : Fin 3) : Code := .seq
  (NatAssign.code (literalStage 0 (Parts.literal 1)))
  (NatAssign.Instruction.code (.add (positivePort 0) (positivePort (17+i.val))))
def cursorValues (i : Fin 3) (j : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (Function.update v 0 (Parts.literal 1)) (17+i.val)
    (NaturalChannel.replace .positive (v (17+i.val)) (j+1))

theorem naturalLiteral_width (j W : ℕ) (hj : j.bits.length ≤ W) (hW : 1 ≤ W) :
    (Parts.literal (j:ℚ)).Width W := by
  simpa only [Parts.literal,Parts.Width,Rat.num_natCast,Rat.den_natCast,Int.toNat_natCast,
    Int.toNat_neg_natCast,Nat.zero_bits,List.length_nil,show (1:ℕ).bits.length=1 by decide]
    using (show j.bits.length ≤ W ∧ 0 ≤ W ∧ 1 ≤ W from ⟨hj,Nat.zero_le W,hW⟩)

theorem cursor_executes {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    (i : Fin 3) (j W : ℕ) (v : ℕ→Parts) (hw : WidthBank termBank W v)
    (hW : 1 ≤ W) (hj : (j+1).bits.length ≤ W) (hv : (v (17+i.val)).positive=j)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : FactorReady a Q N b v s)
    (hr : Ready termBank v s) :
    ∃cost t,Executes input tape (cursorCode i) cost s t ∧ cost ≤ 2*operationCost W+1 ∧
      FactorReady a Q N b (cursorValues i j v) t ∧ Ready termBank (cursorValues i j v) t ∧
      WidthBank termBank W (cursorValues i j v) ∧
      BinaryPrecision.Frame (RationalDataflow.workspace termBank) s.val t.val := by
  have hi : 17+i.val∈termBank := by
    have := i.isLt
    simp only [termBank,tensorBank,Finset.mem_insert,Finset.mem_union,Finset.mem_Ico]
    exact Or.inr (Or.inr ⟨by omega,by omega⟩)
  have h0 : 0∈termBank := by decide
  have hi0 : 17+i.val≠0 := by omega
  have hone : (Parts.literal (1:ℚ)).Width W := naturalLiteral_width 1 W (by simpa using hW) hW
  obtain ⟨c0,s0,e0,hc0,r0,f0⟩ := literal_executes termBank 0 h0 (Parts.literal 1) v W hone hw input tape s hr
  let u := Function.update v 0 (Parts.literal 1)
  have hp0 : positivePort 0∈RationalDataflow.ids termBank := cell_mem h0 (by simp [cellPorts])
  have hpi : positivePort (17+i.val)∈RationalDataflow.ids termBank := cell_mem hi (by simp [cellPorts])
  have hne : positivePort 0≠positivePort (17+i.val) := by simp only [positivePort];omega
  obtain ⟨c1,t,e1,hc1,bank,scratch,f1⟩ := NatAssign.instruction_executes
    (RationalDataflow.ids termBank) (ids_ge termBank)
    (.add (positivePort 0) (positivePort (17+i.val))) ⟨hp0,hpi,hne⟩ (dataValues u)
    input tape s0 r0.1 r0.2
  have hu0 : dataValues u (positivePort 0)=1 := by simp [u,Parts.literal]
  have hui : dataValues u (positivePort (17+i.val))=j := by
    simpa only [dataValues_positive,u,Function.update_of_ne hi0] using hv
  have heq : NatAssign.Instruction.update (.add (positivePort 0) (positivePort (17+i.val)))
      (dataValues u)=dataValues (cursorValues i j v) := by
    simp only [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,hu0,hui]
    rw [show 1+j=j+1 by omega]
    simpa only [NaturalChannel.port,u,Function.update_of_ne hi0,cursorValues] using
      NaturalChannel.replace_dataValues .positive u (17+i.val) (j+1)
  rw [heq] at bank
  have ready : Ready termBank (cursorValues i j v) t := ⟨bank,scratch⟩
  have subset : NatAssign.changed (positivePort (17+i.val)) ⊆ RationalDataflow.workspace termBank := by
    intro k hk
    simp only [NatAssign.changed,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl
    · decide
    · decide
    · decide
    · decide
    · exact Finset.mem_union_right _ hpi
  have frame := f0.trans (f1.mono subset)
  have width : WidthBank termBank W (cursorValues i j v) := by
    apply (hw.update 0 hone).update
    exact ⟨hj,(hw _ hi).2⟩
  refine ⟨c0+c1,t,e0.seq e1,?_,hs.term_frame frame ready,ready,width,frame⟩
  have hwidth : j.bits.length ≤ W := by simpa only [hv] using (hw _ hi).1
  simp only [NatAssign.Instruction.price,hu0,hui,show (1:ℕ).bits.length=1 by decide] at hc1
  have hc : stageCost W+200*(W+5) ≤ 2*operationCost W+1 := by
    unfold stageCost operationCost
    nlinarith only [Nat.zero_le W,Nat.zero_le (W^2)]
  omega

#print axioms cursor_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
