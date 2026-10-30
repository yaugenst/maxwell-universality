import Maxwell.Continuum.FourierTensorTraversalSemantics

/-! Complete execution of the fixed row-major tensor traversal. The loop
body invokes the actual Fourier-to-Chebyshev coefficient compiler. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 6500000
set_option maxRecDepth 32768

theorem tensorTraversal_executes {n B Q N W : ℕ} (d : TensorInput n B Q N W)
    (input : List Bool) (tape : ℕ→Bool) :
    ∀axes : List (Fin 3),axes.Nodup → ∀s (h : TensorState d s),
      TensorBuffers W Finset.univ s → (∀i,i∉axes → h.index i<d.degree) →
      ∃cost t,∃next : TensorState d t,Executes input tape (tensorTraversalCode axes) cost s t ∧
        cost ≤ tensorTraversalCost Q N n W d.degree axes.length ∧
        TensorBuffers W Finset.univ t ∧
        (∀i,i∉axes → next.index i=h.index i) ∧
        t.val.output=(d.payload axes h.index).reverse++s.val.output := by
  intro axes
  induction axes with
  | nil =>
    intro _ s h hb hv
    let j : Fin 3→Fin d.degree := fun i => ⟨h.index i,hv i (by simp)⟩
    obtain ⟨c,t,next,e,hc,hi,ho⟩ := repeatedCoefficient_executes d j input tape s h (fun _ => rfl)
    refine ⟨c,t,next,e,hc,?_,?_,?_⟩
    · apply hb.frame
      intro i _
      exact e.tapesBelow repeatedCoefficient_tapesBelow _ (by omega)
    · intro i _
      exact hi i
    · simpa only [TensorInput.payload,TensorInput.numeratorAt,
        dite_eq_left (fun i => hv i (by simp)),j] using ho
  | cons i is ih =>
    intro hn s h hb hv
    have hni : i∉is := (List.nodup_cons.mp hn).1
    have hns : is.Nodup := (List.nodup_cons.mp hn).2
    obtain ⟨c0,s0,start,e0,hc0,index0,f0⟩ := resetCursor_executes d i input tape s h
    have buffers0 : TensorBuffers W Finset.univ s0 := hb.frame (fun j _ =>
      e0.tapesBelow (resetCursor_tapesBelow i) _ (by omega))
    obtain ⟨old,hold,oldWord⟩ := buffers0 i (Finset.mem_univ _)
    have hsource : BankArray.Word s0.val 1110 d.degree.bits := start.storedDegree
    obtain ⟨s1,e1,count1,f1⟩ := WordReplace.executes 1110 (1101+i.val)
      (by have := i.isLt;omega) input tape d.degree.bits old s0 hsource oldWord
    obtain ⟨origin,count1⟩ := count1
    let initial : TensorState d s1 := start.external_frame f1.2.2.1 (fun k hk =>
      f1.2.2.2.2.2.1 k (by have := i.isLt;omega))
    let inv : ℕ→Store→Prop := fun k st => ∃state : TensorState d st,
      TensorBuffers W (Finset.univ.erase i) st ∧ state.index i=k ∧
      (∀j,j∉i::is → state.index j=h.index j) ∧
      st.val.output=(d.payloadPrefix is i h.index k).reverse++s.val.output
    have stable : ∀k a b,CountedShifted.Frame (1101+i.val) a b → inv k a → inv k b := by
      intro k a b f ⟨state,buffers,index,outside,output⟩
      refine ⟨state.count_frame i f,buffers.count_frame i (by simp) f,index,outside,?_⟩
      exact f.2.2.2.2.1.trans output
    have step : ∀k<d.degree,∀ys a,inv k a →
        a.val.tapes (1101+i.val)=BitTape.shifted ys origin → ys.length=d.degree.bits.length →
        ∃cost t,Executes input tape (.seq (tensorTraversalCode is) (cursorCode i)) cost a t ∧
          inv (k+1) t ∧ t.val.tapes (1101+i.val)=BitTape.shifted ys origin ∧
          cost ≤ tensorTraversalCost Q N n W d.degree is.length+(2*operationCost W+1) := by
      intro k hk ys a ⟨state,buffers,index,outside,output⟩ word length
      have full : TensorBuffers W Finset.univ a := by
        intro j _
        by_cases hji : j=i
        · subst j
          exact ⟨ys,by rw [length];exact d.degreeWidth,origin,word⟩
        · exact buffers j (by simp [hji])
      have valid : ∀j,j∉is → state.index j<d.degree := by
        intro j hj
        by_cases hji : j=i
        · subst j;simpa only [index] using hk
        · have hjc : j∉i::is := by simp [hji,hj]
          rw [outside j hjc]
          exact hv j hjc
      obtain ⟨ca,a1,mid,ea,hca,buffers1,outside1,output1⟩ := ih hns a state full valid
      have index1 : mid.index i=k := (outside1 i hni).trans index
      obtain ⟨cb,t,next,eb,hcb,index2,fb⟩ := advanceCursor_executes d i input tape a1 mid
        (by simpa only [index1] using hk)
      have payloadEq : d.payload is state.index=d.payload is (Function.update h.index i k) := by
        apply d.payload_congr
        intro j hj
        by_cases hji : j=i
        · subst j;simp only [Function.update_self,index]
        · simpa only [Function.update_of_ne hji] using outside j (by simp [hji,hj])
      have nextOutside : ∀j,j∉i::is → next.index j=h.index j := by
        intro j hj
        have hji : j≠i := (by simpa only [List.mem_cons,not_or] using hj : j≠i ∧ j∉is).1
        have hjs : j∉is := (by simpa only [List.mem_cons,not_or] using hj : j≠i ∧ j∉is).2
        rw [index2,Function.update_of_ne hji,outside1 j hjs,outside j hj]
      have nextOutput : t.val.output=(d.payloadPrefix is i h.index (k+1)).reverse++s.val.output := by
        rw [fb.output,output1,payloadEq,output,d.payloadPrefix_succ,List.reverse_append,List.append_assoc]
      have nextBuffers : TensorBuffers W (Finset.univ.erase i) t :=
        (buffers1.restrict (Finset.erase_subset _ _)).frame (fun j _ =>
          eb.tapesBelow (cursor_tapesBelow i) _ (by omega))
      have nextIndex : next.index i=k+1 := by rw [index2,Function.update_self,index1]
      refine ⟨ca+cb,t,ea.seq eb,⟨next,nextBuffers,nextIndex,nextOutside,nextOutput⟩,?_,
        Nat.add_le_add hca hcb⟩
      exact (eb.tapesBelow (cursor_tapesBelow i) _ (by omega)).trans
        ((ea.protectsTape _ (tensorTraversal_protects_counter is i hni)).trans word)
    have initialInv : inv 0 s1 := by
      refine ⟨initial,?_,?_,?_,?_⟩
      · apply (buffers0.restrict (Finset.erase_subset _ _)).frame
        intro j hj
        apply f1.2.2.2.2.2.1
        intro he
        have hji : j=i := by apply Fin.ext;omega
        subst j
        simp at hj
      · change start.index i=0
        rw [index0,Function.update_self]
      · intro j hj
        change start.index j=h.index j
        have hji : j≠i := (by simpa only [List.mem_cons,not_or] using hj : j≠i ∧ j∉is).1
        rw [index0,Function.update_of_ne hji]
      · simpa only [TensorInput.payloadPrefix_zero,List.reverse_nil,List.nil_append]
          using f1.2.2.2.2.1.trans f0.output
    obtain ⟨c2,t,ys,e2,⟨next,buffers2,_index2,outside2,output2⟩,count2,length2,hc2⟩ :=
      forward_counted_executes (1101+i.val) origin (.seq (tensorTraversalCode is) (cursorCode i))
        input tape d.degree d.degree.bits.length
        (tensorTraversalCost Q N n W d.degree is.length+(2*operationCost W+1))
        inv stable step d.degree.bits s1 (addressValue_bits _) count1 rfl initialInv
    have finalBuffers : TensorBuffers W Finset.univ t := by
      intro j _
      by_cases hji : j=i
      · subst j
        exact ⟨ys,by rw [length2];exact d.degreeWidth,origin,count2⟩
      · exact buffers2 j (by simp [hji])
    refine ⟨c0+((6*old.length+15*d.degree.bits.length+21)+c2),t,next,
      e0.seq (e1.seq e2),?_,finalBuffers,outside2,?_⟩
    · have hload : 6*old.length+15*d.degree.bits.length+21 ≤ 21*W+21 := by
        have hd : d.degree.bits.length ≤ W := d.degreeWidth
        omega
      have hcount : c2 ≤ (d.degree+1)*(13*W+15)+
          d.degree*(tensorTraversalCost Q N n W d.degree is.length+(2*operationCost W+1)) := by
        exact hc2.trans (Nat.add_le_add_right
          (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 13 d.degreeWidth) _)) _)
      simpa only [tensorTraversalCost,List.length_cons,Nat.add_assoc] using
        Nat.add_le_add hc0 (Nat.add_le_add hload hcount)
    · exact output2

#print axioms tensorTraversal_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
