import Maxwell.Continuum.FourierTensorTraversalExecution
import Maxwell.Continuum.RealTensorOutput

/-! The runtime traversal emits the declared tensor representation in the
same coordinate order, rather than an alternative list representation. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

theorem range_eq_finRange_values (D : ℕ) : List.range D=(List.finRange D).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

theorem flatMap_range_fin {α : Type*} (D : ℕ) (f : ℕ→List α) :
    (List.range D).flatMap f=(List.finRange D).flatMap (fun i => f i.val) := by
  rw [range_eq_finRange_values]
  simp only [List.flatMap_map]

namespace TensorInput
variable {n B Q N W : ℕ} (d : TensorInput n B Q N W)

def componentPayload : List Bool :=
  ((finalData Finset.univ d.frequency d.amplitude Q N).map Prod.fst).flatMap
    (fun a => Codec.int a.numerator)

theorem payload_component (j : Fin 3→ℕ) : d.payload [0,1,2] j=d.componentPayload := by
  simp only [payload,flatMap_range_fin,componentPayload,finalData,List.map_flatMap,
    List.map_map,List.flatMap_assoc,List.flatMap_map,Function.comp_def]
  congr 1
  funext a
  congr 1
  funext b
  congr 1
  funext c
  have he : Function.update (Function.update (Function.update j 0 a.val) 1 b.val) 2 c.val=
      (fun i : Fin 3 => (![a,b,c] i).val) := by
    funext i
    fin_cases i <;> simp
  rw [he]
  have hb : ∀i : Fin 3,(![a,b,c] i).val<d.degree := fun i => (![a,b,c] i).isLt
  simp only [numeratorAt,dite_eq_left hb]
  rfl

end TensorInput

theorem tensorComponent_executes {n B Q N W : ℕ} (d : TensorInput n B Q N W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : TensorState d s)
    (hb : TensorBuffers W Finset.univ s) :
    ∃cost t,∃_next : TensorState d t,Executes input tape tensorComponentCode cost s t ∧
      cost ≤ tensorTraversalCost Q N n W d.degree 3 ∧ TensorBuffers W Finset.univ t ∧
      t.val.output=d.componentPayload.reverse++s.val.output := by
  have valid : ∀i : Fin 3,i∉[0,1,2] → h.index i<d.degree := by
    intro i hi
    fin_cases i <;> simp at hi
  obtain ⟨c,t,next,e,hc,buffers,_,out⟩ := tensorTraversal_executes d input tape [0,1,2]
    (by decide) s h hb valid
  exact ⟨c,t,next,e,hc,buffers,by simpa only [d.payload_component] using out⟩

#print axioms TensorInput.payload_component
#print axioms tensorComponent_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
