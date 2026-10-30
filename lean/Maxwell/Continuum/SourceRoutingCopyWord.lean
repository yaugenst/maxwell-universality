import Maxwell.Continuum.SourceRoutingGeometryLoad

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured
open RationalAccumulator (Word)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem copyWord_executes (source target old value : ℕ) (different : source≠target)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (sourceWord : Word s.val source value) (targetWord : Word s.val target old) :
    ∃steps t,Executes input tape (loadCode source target) steps s t ∧
      steps ≤ 6*old.bits.length+15*value.bits.length+21 ∧ Word t.val target value ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨origin,ho⟩:=targetWord
  obtain ⟨co,hco⟩:=sourceWord
  obtain ⟨a,ea,atapes,af⟩:=WordCall.clear target input tape old.bits origin s ho
  have sourceA : a.val.tapes source=BitTape.shifted value.bits co := by simpa [atapes,different] using hco
  have blankA : a.val.tapes target={BitTape.blank with head:=origin+old.bits.length} := by simp [atapes]
  obtain ⟨t,et,ttapes,tf⟩:=WordCall.clone source target different input tape value.bits co
    (origin+old.bits.length) a sourceA blankA
  have keep (j : ℕ) (hj : j≠target) : t.val.tapes j=s.val.tapes j := by simp [ttapes,atapes,hj]
  exact ⟨_,t,ea.seq et,by omega,⟨origin+old.bits.length,by simp [ttapes]⟩,
    ⟨tf.1.trans af.1,tf.2.1.trans af.2.1,tf.2.2.1.trans af.2.2.1,
      tf.2.2.2.1.trans af.2.2.2.1,tf.2.2.2.2.1.trans af.2.2.2.2.1,
      fun j hj => keep j (by simpa only [Finset.mem_singleton] using hj)⟩⟩

theorem bank_of_frame {v : ℕ→ℕ} {changed : Finset ℕ} {s t : BitRAMState}
    (bank : NatAssign.Bank ids v s) (frame : BinaryPrecision.Frame changed s t) (outside : Disjoint ids changed) :
    NatAssign.Bank ids v t := fun j hj =>
  RationalAccumulator.word_of_eq (frame.tapes j (Finset.disjoint_left.mp outside hj)) (bank j hj)

#print axioms copyWord_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
