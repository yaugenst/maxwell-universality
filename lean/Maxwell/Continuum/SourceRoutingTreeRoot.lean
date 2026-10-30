import Maxwell.Continuum.SourceRoutingTreeChildren
import Maxwell.Continuum.SourceRoutingTreeStepCost

/-! The root executes the same reusable split program on the completed
source permutation, and exposes the stored logical children for the tree. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Root
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem executes (q : ℕ→ℕ) (rows columns B : ℕ)
    (hn : q 801=2*2^(columns+rows)) (hw : q 802=columns+rows+2)
    (hq : ∀i∈NodeSetup.controls,(q i).bits.length ≤ B)
    (target : Targets.Target rows (columns+1))
    (hsource : IncidenceEncoding.Separated (q 803) ((q 801)*(q 802)) (q 804) ((q 801)*(q 802)))
    (hforward : q 803+(q 801)*(q 802) ≤ q 800)
    (hbackward : q 804+(q 801)*(q 802) ≤ q 800)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids q s.val) (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839)
    (hf : Storage.Permutation rows (columns+1) target s.val.memory (q 803) (q 802))
    (hb : Storage.Permutation rows (columns+1) target.symm s.val.memory (q 804) (q 802)) :
    ∃steps t, Executes input tape PrivateVisit.code steps s t ∧
      steps ≤ 2^180*(q 801+1)*(B+2)^3 ∧
      NatAssign.Bank Division.ids q t.val ∧ PrivateVisit.Clean t ∧ Blank t.val 839 ∧
      Outputs.At (q 800) (q 801) (q 802) 0 rows columns target t.val.memory ∧
      PrivateNode.Frame s.val t.val ∧
      Memory.Frame (q 800) (stride (q 801) (q 802)) s.val.memory t.val.memory := by
  have subset : NodeSetup.controls⊆Division.ids := by decide
  obtain ⟨steps,t,he,hcost,rep,zt,_,ft,mt⟩:=PrivateVisit.executes q (columns+rows) B hn hw hq
    (ColorData.splitData rows columns target) (ColorData.splitData_colors rows columns target)
    hsource hforward hbackward input tape s hc (fun i hi => hs i (subset hi))
    ((Storage.split_target rows columns target _ _ _).mp hf)
    ((Storage.split_inverse rows columns target _ _ _).mp hb)
  have bt : NatAssign.Bank Division.ids q t.val := by
    intro i hi
    exact RationalAccumulator.word_of_eq (ft.tapes i (Or.inr (Division.ids_lower i hi))
      (Step.private_keep i hi).1 (Step.private_keep i hi).2) (hs i hi)
  have layout : Node.layout (NodeSetup.descriptor q)=RoutingAllocator.layout (q 800)
      (2*2^(columns+rows)) (columns+rows+2) (q 803) (q 804) := by
    rw [NodeWords.layout_eq]
    dsimp only [NodeWords.plainLayout]
    rw [hn,hw]
  have stored:=Outputs.of_represents rep
  rw [layout] at stored mt
  have hblock : block (q 800) (q 801) (q 802) 0=q 800 := by simp [block]
  rw [←hblock] at stored mt
  have norm : Outputs.At (q 800) (q 801) (q 802) 0 rows columns target t.val.memory :=
    (Outputs.at_iff _ _ _ 0 rows columns (q 803) (q 804) target _).mp stored
  have frame:=Memory.split_frame (q 800) (q 801) (q 802) 0 (columns+rows)
    (by omega) (by omega) (q 803) (q 804) s.val.memory t.val.memory mt
  rw [hblock] at frame
  exact ⟨steps,t,he,hcost.trans (NodeWords.visit_bound q (columns+rows) B hn hw hq),bt,zt,
    RationalAccumulator.blank_of_eq (ft.tapes 839 (by omega) (by omega) (by decide)) h839,norm,ft,frame⟩

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Root
