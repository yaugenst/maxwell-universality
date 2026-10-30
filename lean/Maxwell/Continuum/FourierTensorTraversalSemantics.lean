import Maxwell.Continuum.FourierTensorTraversalCode

/-! Row-major tensor payload semantics, independent of the temporary
values of indices which the traversal resets before using them. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 2500000

namespace TensorInput
variable {n B Q N W : ℕ} (d : TensorInput n B Q N W)

theorem payload_congr (axes : List (Fin 3)) (j k : Fin 3→ℕ)
    (h : ∀i,i∉axes → j i=k i) : d.payload axes j=d.payload axes k := by
  induction axes generalizing j k with
  | nil =>
    have he : j=k := funext (fun i => h i (by simp))
    rw [he]
  | cons i is ih =>
    simp only [payload]
    congr 1
    funext r
    apply ih
    intro l hl
    by_cases hli : l=i
    · subst l;simp
    · simp only [Function.update_of_ne hli]
      exact h l (by simp [hli,hl])

def payloadPrefix (axes : List (Fin 3)) (i : Fin 3) (j : Fin 3→ℕ) (k : ℕ) : List Bool :=
  (List.range k).flatMap fun r => d.payload axes (Function.update j i r)

theorem payloadPrefix_zero (axes : List (Fin 3)) (i : Fin 3) (j : Fin 3→ℕ) :
    d.payloadPrefix axes i j 0=[] := rfl

theorem payloadPrefix_succ (axes : List (Fin 3)) (i : Fin 3) (j : Fin 3→ℕ) (k : ℕ) :
    d.payloadPrefix axes i j (k+1)=
      d.payloadPrefix axes i j k++d.payload axes (Function.update j i k) := by
  simp only [payloadPrefix,List.range_succ,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]

end TensorInput

#print axioms TensorInput.payload_congr
end Maxwell.Continuum.Profile.WaveMachine.Runtime
