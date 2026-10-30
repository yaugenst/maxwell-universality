import Maxwell.Continuum.FourierTensorMachineRows

/-! Literal machine execution of one complete Fourier-to-tensor
coefficient contraction, including initialization and all cached reads. -/

namespace Maxwell.Continuum.Profile.TensorMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open scoped BigOperators
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def coefficientCode : Code :=
  .seq (NatAssign.code (literalStage 0 (Parts.literal 0))) (rowFoldCode 8 readPlan body)

def coefficientCost (n W wordLength : ℕ) : ℕ :=
  stageCost (accumulatorWidth n W)+(n+1)*(13*wordLength+15)+
    n*rowFoldStepCost 8 3 (accumulatorWidth n W) readPlan body

theorem coefficient_executes {n : ℕ} (a : Table (8*n)) (W : ℕ) (hW : 1≤W)
    (hmeta : a.MetadataWidth W) (haValid : ∀i,(a.get i).Valid)
    (v : ℕ→Parts) (hv : WidthBank ids W v) (hg : Good ids v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : Ready ids v s) (ha : a.Ready s)
    (hz : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t output,Executes input tape coefficientCode cost s t ∧
      cost≤coefficientCost n W xs.length ∧ Ready ids output t ∧ Good ids output ∧ a.Ready t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      WidthBank ids (accumulatorWidth n W) output ∧
      (output 0).value=∑i∈Finset.range n,rowTerm a i := by
  have haWidth : ∀i,(a.get i).Width W := a.get_width W hmeta s ha
  let start := Function.update v 0 (Parts.literal 0)
  have hsWidth : WidthBank ids W start := hv.update 0
    ((Parts.literal_width RationalWords.width_zero').mono hW)
  have hsGood : Good ids start := hg.update 0 (Parts.literal_valid 0)
  have hB : W≤accumulatorWidth n W := by unfold accumulatorWidth;omega
  have hzero : (Parts.literal (0 : ℚ)).Width (accumulatorWidth n W) :=
    (Parts.literal_width RationalWords.width_zero').mono (hW.trans hB)
  obtain ⟨c0,t0,e0,h0,b0,f0⟩ := literal_executes ids 0 (by simp [ids]) (Parts.literal 0) v
    (accumulatorWidth n W) hzero (hv.mono hB) input tape s hs
  have t0a := ha.arithmetic_frame ids f0 b0.2
  have t0z : ∀i∈RowIndex.ids,RationalAccumulator.Blank t0.val i := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f0.tapes i _) (hz i hi)
    apply outside_workspace ids i
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have hmono {k : ℕ} (hk : k≤n) : accumulatorWidth k W≤accumulatorWidth n W := by
    unfold accumulatorWidth
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) W
  have before (k : ℕ) (hk : k<n) :
      WidthBank ids (accumulatorWidth n W) (rowIterate a 8 readPlan body n start k) :=
    (tensor_iterate_width a n W hW haWidth start hsWidth k).mono (hmono hk.le)
  have trace (k : ℕ) (hk : k<n) :
      body.WidthTrace ids (accumulatorWidth n W) (rowLoaded a 8 readPlan body n start k) := by
    have hb := body_widthTrace (rowLoad a (n-1-k) (rowIterate a 8 readPlan body n start k))
      (accumulatorWidth k W) W
      (rowLoad_width a _ _ W hW (by unfold accumulatorWidth;omega) haWidth _
        (tensor_iterate_width a n W hW haWidth start hsWidth k))
      (rowLoad_inputs_width a _ W hW haWidth _)
    apply hb.mono
    have he : accumulatorWidth k W+22*W+22=accumulatorWidth (k+1) W := by
      unfold accumulatorWidth;ring
    rw [he]
    exact hmono (by omega)
  have good (k : ℕ) (_hk : k<n) : Good ids (rowLoaded a 8 readPlan body n start k) :=
    rowLoad_good a _ haValid _ (tensor_iterate_good a n haValid start hsGood k)
  have indices (k : ℕ) (hk : k<n) : ∀x∈readPlan,8*(n-1-k)+x.1<8*n := by
    intro x hx
    have hx7 : x.1≤7 := by
      simp only [readPlan,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with h|h|h|h|h|h|h|h <;> subst x <;> decide
    omega
  obtain ⟨c1,t,_,e1,b1,a1,z1,_,_,h1⟩ := rowFold_executes a ids 8 3 readPlan readPlan_valid
    readPlan_offsets body body_valid n start (accumulatorWidth n W) (hmeta.mono hB)
    before trace good (fun _ _ => body_admissible _) indices input tape xs origin (hlen.trans hB)
    t0 hn ((f0.tapes 201 (outside_workspace ids 201 (by decide))).trans hcount) b0 t0a t0z
  refine ⟨c0+c1,t,rowIterate a 8 readPlan body n start n,e0.seq e1,?_,b1,
    tensor_iterate_good a n haValid start hsGood n,a1,z1,
    tensor_iterate_width a n W hW haWidth start hsWidth n,?_⟩
  · unfold coefficientCost
    omega
  · rw [tensor_iterate_value a n haValid start hsGood n]
    simp only [start,Function.update_self,Parts.literal_value,zero_add]
    exact Finset.sum_range_reflect (rowTerm a) n

theorem coefficient_computes {n : ℕ} (a : Table (8*n)) (W : ℕ) (hW : 1≤W)
    (hmeta : a.MetadataWidth W) (haValid : ∀i,(a.get i).Valid)
    (v : ℕ→Parts) (hv : WidthBank ids W v) (hg : Good ids v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : Ready ids v s) (ha : a.Ready s)
    (hz : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ t output,
      (runPriced (coefficientCode.compile.next input tape) (coefficientCost n W xs.length+1)
        s.val).finished=some (t.place coefficientCode.size) ∧
      (runPriced (coefficientCode.compile.next input tape) (coefficientCost n W xs.length+1)
        s.val).instructions≤coefficientCost n W xs.length ∧ Ready ids output t ∧ a.Ready t ∧
      (output 0).value=∑i∈Finset.range n,rowTerm a i := by
  obtain ⟨cost,t,output,he,hc,hb,_,ha',_,_,hv'⟩ := coefficient_executes a W hW hmeta haValid
    v hv hg input tape xs origin hlen s hn hcount hs ha hz
  obtain ⟨hrun,hsteps⟩ := he.compiled_run (coefficientCost n W xs.length+1) (by omega)
  exact ⟨t,output,hrun,hsteps ▸ hc,hb,ha',hv'⟩

#print axioms coefficient_executes
#print axioms coefficient_computes
end Maxwell.Continuum.Profile.TensorMachine
