import Maxwell.Continuum.PhaseRuntimeDataflowFrame

/-! Fixed phase calls load their preserved range and precision from actual
external words. The loads and cleanup are included in the execution charge. -/
namespace Maxwell.Continuum.RationalDataflow.Phase.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def loadedCode (base : RationalTaylor.Runtime.Cycle) (target source rangePort precisionPort : ℕ) : Code :=
  .seq (WordReplace.code rangePort 652)
    (.seq (WordReplace.code precisionPort 653) (code base target source))

theorem loaded_executes (S : Finset ℕ) (base : RationalTaylor.Runtime.Cycle)
    (Q N oldQ oldN target source rangePort precisionPort W : ℕ)
    (ht : target∈S) (hs' : source∈S) (hrange : 658 ≤ rangePort) (hprecision : 658 ≤ precisionPort)
    (v : ℕ→Parts) (hw : WidthBank S W v) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (holdQ : oldQ.bits.length≤W) (holdN : oldN.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) (hz : Clean s.val)
    (hqo : Word s.val 652 oldQ) (hno : Word s.val 653 oldN)
    (hqr : Word s.val rangePort Q) (hnr : Word s.val precisionPort N) :
    ∃cost t,Executes input tape (loadedCode base target source rangePort precisionPort) cost s t ∧
      cost≤64*(W+1)+costBound Q N W ∧
      Ready S (Function.update v target (Phase.result (RationalTaylor.Runtime.cycleSigns base) Q N (v source))) t ∧
      Clean t.val ∧ Word t.val 652 Q ∧ Word t.val 653 N ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨s0,e0,q0,f0⟩ := WordReplace.executes rangePort 652 (by omega)
    input tape Q.bits oldQ.bits s hqr hqo
  have r0 := hs.wordReplace_frame (parameter_outside_workspace S 652 (by omega)) f0
  have z0 := hz.wordReplace_frame (by omega : (652:ℕ)=652 ∨ 652=653) f0
  have n0 := word_of_eq (f0.2.2.2.2.2.1 653 (by decide)) hno
  have nr0 := word_of_eq (f0.2.2.2.2.2.1 precisionPort (by omega)) hnr
  obtain ⟨s1,e1,n1,f1⟩ := WordReplace.executes precisionPort 653 (by omega)
    input tape N.bits oldN.bits s0 nr0 n0
  have r1 := r0.wordReplace_frame (parameter_outside_workspace S 653 (by omega)) f1
  have z1 := z0.wordReplace_frame (by omega : (653:ℕ)=652 ∨ 653=653) f1
  have q1 := word_of_eq (f1.2.2.2.2.2.1 652 (by decide)) q0
  obtain ⟨c,t,e,hc,rt,zt,qt,nt,ft⟩ := executes S base Q N target source ht hs' v W hw hQ hN hW
    input tape s1 r1 z1 q1 n1
  refine ⟨_,t,e0.seq (e1.seq e),?_,rt,zt,qt,nt,
    (parameter_copy_frame (by omega : (652:ℕ)=652 ∨ 652=653) f0).trans
      ((parameter_copy_frame (by omega : (653:ℕ)=652 ∨ 653=653) f1).trans ft)⟩
  omega

#print axioms loaded_executes
end Maxwell.Continuum.RationalDataflow.Phase.Runtime
