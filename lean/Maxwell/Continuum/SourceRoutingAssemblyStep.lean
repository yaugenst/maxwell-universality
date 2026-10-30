import Maxwell.Continuum.SourceRoutingAssemblyCoordinates
import Maxwell.Continuum.SourceRoutingAssemblyNode
import Maxwell.Continuum.SourceRoutingTreeStep

/-! The reverse inner-loop body computes its addresses, assembles one
node from stored children, and advances the local node index. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyStep
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values Step.increment (AssemblyDescriptor.output v)
def code : Code := .seq AssemblyDescriptor.code (.seq PrivateAssembly.code (NatAssign.code Step.increment))
def cost (v : ℕ→ℕ) (B : ℕ) : ℕ := 2^120*(B+2)^2+
  2^45*(2*v 811+1)*(AssemblyDescriptor.wordBound B+2)^2+
  3000*8^2*(AssemblyDescriptor.wordBound B+2)^2

theorem executes (v : ℕ→ℕ) (heap rootCount rootWidth d rows columns B : ℕ) (i : Fin (2^d))
    (hc : AssemblyCoordinates.Stored v heap rootCount rootWidth d (columns+rows) i.val)
    (hn : 2*2^(columns+rows) ≤ rootCount) (hw : columns+rows+2 ≤ rootWidth) (hB : 4 ≤ B)
    (hz : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (hv : ∀j∈Division.ids,(v j).bits.length ≤ B)
    (target : Targets.Target rows (columns+1))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hclean : PrivateVisit.Clean s) (h839 : Blank s.val 839)
    (colors : Outputs.At heap rootCount rootWidth (levelNode d i) rows columns target s.val.memory)
    (labels : ∀b,StoredLabels rows columns (ColorData.childTarget rows columns target b) s.val.memory
      (Leaves.labelBase heap rootCount rootWidth (child (levelNode d i) b) (2^(columns+rows)) (columns+rows+1))
      (columns+rows+1)) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost v B ∧
      NatAssign.Bank Division.ids (output v) t.val ∧ PrivateVisit.Clean t ∧ Blank t.val 839 ∧
      StoredLabels rows (columns+1) target t.val.memory
        (Leaves.labelBase heap rootCount rootWidth (levelNode d i) (2*2^(columns+rows)) (columns+rows+2))
        (columns+rows+2) ∧ Step.Frame s.val t.val ∧
      Memory.Frame (block heap rootCount rootWidth (levelNode d i)) (stride rootCount rootWidth)
        s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,b0,z0,a839,f0⟩:=AssemblyDescriptor.executes v B hB hc.two hz hv input tape s hs hclean h839
  have wd:=AssemblyDescriptor.output_word_width v B hB hv
  have subset : Assembly.controls⊆Division.ids := by decide
  obtain ⟨c1,b,e1,h1,rep,z1,f1,m1⟩:=AssemblyNode.executes heap rootCount rootWidth (levelNode d i)
    rows columns (AssemblyDescriptor.wordBound B) (AssemblyDescriptor.output v)
    (by dsimp only [AssemblyDescriptor.wordBound];exact Nat.succ_le_of_lt (by positivity)) hn hw
    (AssemblyCoordinates.count v heap rootCount rootWidth d (columns+rows) i.val hc)
    (AssemblyCoordinates.descriptor_layout v heap rootCount rootWidth d (columns+rows) i hc)
    (fun j hj => wd j (subset hj)) target input tape a z0 (fun j hj => b0 j (subset hj))
    (by simpa only [f0.memory] using colors) (by simpa only [f0.memory] using labels)
  have bank : NatAssign.Bank Division.ids (AssemblyDescriptor.output v) b.val := by
    intro j hj
    exact RationalAccumulator.word_of_eq (f1.tapes j (Or.inr (Division.ids_lower j hj))
      (Step.private_keep j hj).1 (Step.private_keep j hj).2) (b0 j hj)
  have b839 : Blank b.val 839 := RationalAccumulator.blank_of_eq
    (f1.tapes 839 (by omega) (by omega) (by decide)) a839
  have vi : ∀a∈Step.increment,a.Valid Division.ids := by
    simp [Step.increment,NatAssign.Instruction.Valid,Division.ids,Division.controls]
  have li : ∀a∈Step.increment,a.literalWidth ≤ AssemblyDescriptor.wordBound B := by
    simp [Step.increment,NatAssign.Instruction.literalWidth,AssemblyDescriptor.wordBound]
    exact Nat.succ_le_of_lt (by positivity)
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩:=Arithmetic.stage Step.increment vi (AssemblyDescriptor.output v)
    (AssemblyDescriptor.wordBound B) wd li input tape b bank z1
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,z2,
    RationalAccumulator.blank_of_eq (f2.tapes 839 (by decide)) b839,?_,?_,?_⟩
  · change c2 ≤ 3000*8^2*(AssemblyDescriptor.wordBound B+2)^2 at h2
    rw [AssemblyDescriptor.output_count,hc.two] at h1
    dsimp only [cost];omega
  · simpa only [f2.memory] using rep
  · refine ⟨f2.inputHead.trans (f1.inputHead.trans f0.inputHead),
      f2.randomCursor.trans (f1.randomCursor.trans f0.randomCursor),
      f2.output.trans (f1.output.trans f0.output),?_⟩
    intro j hj h37 hd hp
    exact (f2.tapes j (fun hm => hd (Arithmetic.work_subset hm))).trans
      ((f1.tapes j hj h37 hp).trans (f0.tapes j hd))
  · intro p hp
    exact (congrFun f2.memory p).trans ((m1 p hp).trans (congrFun f0.memory p))

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyStep
