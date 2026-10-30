import Maxwell.Continuum.SourceRoutingTreeStartupPlan

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.TreeStartup
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem powered_base (total forward backward : ℕ) : powered total forward backward 800=heap total backward := by
  rw [powered,Function.update_of_ne (by decide : (800 : ℕ)≠813),
    selected_other _ _ _ _ (by decide) (by decide),Prepare.output_base,Prepare.output_heap]
  rfl

theorem output_count (total forward backward : ℕ) : output total forward backward 801=count total := by
  rw [output,Allocation.output_count,powered,Function.update_of_ne (by decide : (807 : ℕ)≠813),
    selected_other _ _ _ _ (by decide) (by decide),Prepare.output_rootCount]
  rfl

theorem output_base (total forward backward : ℕ) : output total forward backward 800=heap total backward := by
  rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),
    Prepare.output_base,Prepare.output_heap]
  rfl

theorem output_width (total forward backward : ℕ) : output total forward backward 802=wordWidth total := by
  rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_width]
  rfl

theorem output_forward (total forward backward : ℕ) : output total forward backward 803=forward := by
  rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_forward]
  rfl

theorem output_backward (total forward backward : ℕ) : output total forward backward 804=backward := by
  rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_backward]
  rfl

theorem bits_bounded (total forward backward : ℕ) (hf : forward ≤ heap total backward) :
    bits total forward backward ≤
      4*ControllerWidth.baseWidth (heap total backward) (count total) (wordWidth total) total+4 := by
  let L:=ControllerWidth.baseWidth (heap total backward) (count total) (wordWidth total) total
  have positive : 0<(2 : ℕ)^total := by positivity
  have each (n : ℕ) (hn : n ≤ ControllerWidth.ceiling (heap total backward) (count total) (wordWidth total) total) :
      n.bits.length ≤ L := Maxwell.Continuum.RationalWords.bits_mono hn
  have n:=each (count total) (by dsimp only [ControllerWidth.ceiling];omega)
  have w:=each (wordWidth total) (by dsimp only [ControllerWidth.ceiling];omega)
  have f:=each forward (by dsimp only [ControllerWidth.ceiling];omega)
  have b:=each backward (by dsimp only [ControllerWidth.ceiling,heap];omega)
  dsimp only [bits]
  omega

theorem output_words (total forward backward : ℕ) (hf : forward ≤ heap total backward) :
    ∀i∈Division.ids,(output total forward backward i).bits.length ≤
      Traversal.width (heap total backward) total total := by
  have bounded:=bits_bounded total forward backward hf
  have numerical : 4*(16*(stageBits total forward backward+1)+1) ≤
      Traversal.width (heap total backward) total total := by
    dsimp only [Traversal.width,Level.uniformWidth,stageBits]
    change bits total forward backward ≤
      4*ControllerWidth.baseWidth (heap total backward) (2^(total+total)) (total+total+1) total+4 at bounded
    omega
  intro i hi
  exact (output_words_raw total forward backward i hi).trans numerical

theorem root_setup (total forward backward : ℕ) (ht : 1 ≤ total) (hf : forward ≤ heap total backward) :
    RootRun.Setup (output total forward backward) (heap total backward) total total := by
  refine ⟨⟨ht,?_,?_,output_depth total forward backward,?_,?_,?_,?_,?_,?_,?_,output_words total forward backward hf⟩,
    output_base total forward backward,output_count total forward backward,output_width total forward backward⟩
  · rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_heap]
    rfl
  · rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_stride]
    rfl
  · rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_currentCount]
    rfl
  · rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_currentWidth]
    rfl
  · exact Allocation.output_population _
  · rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_other _ _ (by decide)]
    rfl
  · rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_other _ _ (by decide)]
    rfl
  · rw [output_other _ _ _ _ (by decide) (by decide) (by decide) (by decide),Prepare.output_two]
  · intro i hi
    have different : i≠801 ∧ i≠813 := by
      simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    rw [output,Allocation.output_other _ _ different.1 different.2]
    exact powered_zero total forward backward i hi

#print axioms output_words
#print axioms root_setup
end Maxwell.Cost.RoutingPorts.Complete.Tree.TreeStartup
