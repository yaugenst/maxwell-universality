import Maxwell.Continuum.ChebyshevWaveFactorState

/-! One actual save/reset call closes the workspace transition between
successive tensor factors, including erasure of the old large accumulators. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem factorFinish_executes {n D : ℕ} (a : Table n) (b : Table (2*D))
    (Q N W B target : ℕ) (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W) (hW : 6 ≤ W)
    (ht : 17 ≤ target) (ht' : target+1<32) (v : ℕ→Parts) (hw : WidthBank tensorBank B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready tensorBank v s) (hp : Phase.Runtime.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (hc : NatAssign.Bank resetIds (completedSetup Q N) s.val)
    (ha : a.Ready s) (hb : b.OutputReady s) (hz : Blank s.val 680)
    (hsv : ∀i∈savedPorts,Blank s.val i) :
    ∃cost t,Executes input tape (factorFinishCode target) cost s t ∧
      cost ≤ factorFinishCost Q N W B ∧ FactorReady a Q N b (factorValues target v) t ∧
      t.val.tapes 1048=s.val.tapes 1048 := by
  have ht0 : target∈tensorBank := by simp [tensorBank,Finset.mem_Ico];omega
  have ht1 : target+1∈tensorBank := by simp [tensorBank,Finset.mem_Ico];omega
  obtain ⟨c0,s0,e0,h0,r0,w0,f0⟩ := partsCopy_executes tensorBank 8 target (by decide) ht0 (by omega)
    v B hw input tape s hs
  obtain ⟨c1,s1,e1,h1,r1,w1,f1⟩ := partsCopy_executes tensorBank 9 (target+1) (by decide) ht1 (by omega)
    (Function.update v target (v 8)) B w0 input tape s0 r0
  have get9 : (Function.update v target (v 8)) 9=v 9 := Function.update_of_ne (by omega) _ _
  rw [get9] at r1 w1
  change Ready tensorBank (factorSaveValues target v) s1 at r1
  change WidthBank tensorBank B (factorSaveValues target v) at w1
  have hvalid : ∀a∈cacheResetInstructions,a.Valid tensorBank := by
    simp [cacheResetInstructions,RationalDataflow.Instruction.Valid,tensorBank,ids]
  have htrace := inferred_widthTrace tensorBank cacheResetInstructions hvalid
    (fun _ => B) (factorSaveValues target v) w1 _ (w1.mono (by omega)) (cacheReset_program_width B)
  obtain ⟨c2,s2,e2,h2,r2,f2⟩ := program_executes tensorBank cacheResetInstructions hvalid
    (factorSaveValues target v) (B+1) htrace input tape s1 r1
  change Ready tensorBank (factorValues target v) s2 at r2
  have fa := f0.trans (f1.trans f2)
  have hbank : NatAssign.Bank resetIds (completedSetup Q N) s2.val := by
    intro i hi
    have hd : Disjoint resetIds (RationalDataflow.workspace tensorBank) := by decide
    exact word_of_eq (fa.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (hc i hi)
  obtain ⟨c3,t,e3,h3,b3,p3,count3,z3,f3⟩ := reset_executes Q N W hQ hN hW input tape s2 hbank r2.2
  have phase2 := hp.arithmetic_frame fa r2
  have floor2 := hf.arithmetic_frame fa
  have source2 := ha.arithmetic_frame tensorBank fa r2.2
  have output2 := output_tensor_frame hb fa r2.2
  have inner2 := blank_of_eq (fa.tapes 680 (outside_workspace tensorBank 680 (by decide))) hz
  have saved2 : ∀i∈savedPorts,Blank s2.val i := by
    intro i hi
    have hr := savedPorts_range i hi
    exact blank_of_eq (fa.tapes i (outside_workspace tensorBank i (by omega))) (hsv i hi)
  refine ⟨(c0+c1)+(c2+c3),t,(e0.seq e1).seq (e2.seq e3),?_,
    ⟨tensor_setup_ready_frame r2 f3 z3,setup_phase_frame phase2 f3,setup_floor_frame floor2 f3,
      b3,setup_table_frame source2 f3 z3,setup_output_frame output2 f3 z3,p3,count3,
      blank_of_eq (f3.tapes 680 (by decide)) inner2,?_⟩,
    (f3.tapes 1048 (by decide)).trans (fa.tapes 1048 (by decide))⟩
  · have h2' : c2 ≤ 12*operationCost (B+1)+1 := by simpa only [show cacheResetInstructions.length=12 by rfl] using h2
    unfold factorFinishCost
    omega
  · intro i hi
    have hd : Disjoint savedPorts setupWorkspace := by decide
    exact blank_of_eq (f3.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (saved2 i hi)

#print axioms factorFinish_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
