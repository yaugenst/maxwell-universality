import Maxwell.Continuum.FourierTensorDeclaredPayload
import Maxwell.Continuum.FourierTensorTraversalCost

/-! A single fixed compiled Boolean machine emits the declared scalar
tensor payload. The running-time theorem includes every runtime traversal. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

theorem tensorComponent_compiled_run {n B Q N W : ℕ} (d : TensorInput n B Q N W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : TensorState d s)
    (hb : TensorBuffers W Finset.univ s) :
    ∃t,Nonempty (TensorState d t) ∧ TensorBuffers W Finset.univ t ∧
      (runPriced (tensorComponentCode.compile.next input tape)
        (tensorTimeCoefficient*(n+1)^3*(Q+N+W+64)^243+1) s.val).finished=
          some (t.place tensorComponentCode.size) ∧
      t.val.output=d.componentPayload.reverse++s.val.output := by
  obtain ⟨c,t,next,e,hc,buffers,out⟩ := tensorComponent_executes d input tape s h hb
  have hcost := hc.trans (tensorTraversalCost_polynomial Q N n W)
  obtain ⟨run,_⟩ := e.compiled_run (tensorTimeCoefficient*(n+1)^3*(Q+N+W+64)^243+1) (by omega)
  exact ⟨t,⟨next⟩,buffers,run,out⟩

theorem tensorComponent_compiled_run_polylog {n B Q N W : ℕ} (d : TensorInput n B Q N W)
    (C ell : ℕ) (hell : 1 ≤ ell) (hX : Q+N+W+64 ≤ C*ell^16) (hn : n+1 ≤ C*ell^33)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : TensorState d s)
    (hb : TensorBuffers W Finset.univ s) :
    ∃t,Nonempty (TensorState d t) ∧ TensorBuffers W Finset.univ t ∧
      (runPriced (tensorComponentCode.compile.next input tape)
        ((tensorTimeCoefficient*C^246)*ell^4096+1) s.val).finished=
          some (t.place tensorComponentCode.size) ∧
      t.val.output=d.componentPayload.reverse++s.val.output := by
  obtain ⟨c,t,next,e,hc,buffers,out⟩ := tensorComponent_executes d input tape s h hb
  have hcost := hc.trans (tensorTraversalCost_source_exponent Q N n W C ell hell hX hn)
  obtain ⟨run,_⟩ := e.compiled_run ((tensorTimeCoefficient*C^246)*ell^4096+1) (by omega)
  exact ⟨t,⟨next⟩,buffers,run,out⟩

end Maxwell.Continuum.Profile.WaveMachine.Runtime

namespace Maxwell.Continuum.Profile
open Maxwell.Cost
set_option maxHeartbeats 2000000

def realComponentPayload {n B : ℕ} (q : Fin n→Fin 3→ℚ) (a : Fin n→ComplexDyadic B)
    (Q N : ℕ) : List Bool :=
  ((finalData Finset.univ q a Q N).map Prod.fst).flatMap (fun x => Codec.int x.numerator)

theorem realFinalVector_payload {n B : ℕ} (q : Fin n→Fin 3→ℚ)
    (a : Fin 3→Fin n→ComplexDyadic B) (Q N : ℕ) :
    (realFinalVectorData Finset.univ q a Q N).flatMap (fun x => Codec.int x.numerator)=
      realComponentPayload q (a 0) Q N++realComponentPayload q (a 1) Q N++
        realComponentPayload q (a 2) Q N := by
  simp only [realFinalVectorData,finalVectorData,List.map_flatMap,List.flatMap_assoc]
  rw [show List.finRange 3=[0,1,2] by decide]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,realComponentPayload,List.append_assoc]

theorem realFinalVectorBits_components {n B : ℕ} (q : Fin n→Fin 3→ℚ)
    (a : Fin 3→Fin n→ComplexDyadic B) (Q N : ℕ) :
    realFinalVectorBits Finset.univ q a Q N=
      Codec.nat (B+(waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N))++
      Codec.nat (3*(waveDegree (8*Q) N)^3)++
      realComponentPayload q (a 0) Q N++realComponentPayload q (a 1) Q N++
      realComponentPayload q (a 2) Q N := by
  simp only [realFinalVectorBits,Codec.list,realFinalVectorData_length,realFinalVector_payload,
    List.append_assoc]

#print axioms WaveMachine.Runtime.tensorComponent_compiled_run_polylog
#print axioms realFinalVectorBits_components
end Maxwell.Continuum.Profile
