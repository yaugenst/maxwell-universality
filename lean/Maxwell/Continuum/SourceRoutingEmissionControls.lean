import Maxwell.Continuum.SourceRoutingEmissionLoop
import Maxwell.Cost.WordReplace
import Maxwell.Cost.Structured.WordLiteral

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

theorem State.copy_count {V E : Type*} {half : ℕ} {data : Gluing.Data V E half}
    {p : Plan (2*half)} {cursor index : ℕ} {s : Store} (state : State data p cursor index s)
    (source value : ℕ) (different : source≠1258) (input : List Bool) (tape : ℕ→Bool)
    (sourceWord : Word s.val source value) (blank : Blank s.val 1258) :
    ∃t,Executes input tape (WordReplace.code source 1258) (15*value.bits.length+21) s t ∧
      State data p cursor index t ∧ Word t.val 1258 value ∧
      BinaryPrecision.Frame {1258} s.val t.val := by
  have empty : BankArray.Word s.val 1258 []:=(RationalAccumulator.zero_word_iff_blank _ _).mpr blank
  obtain ⟨t,he,word,frame⟩:=WordReplace.executes source 1258 different input tape value.bits [] s sourceWord empty
  have ft : BinaryPrecision.Frame {1258} s.val t.val:=
    ⟨frame.1,frame.2.1,frame.2.2.1,frame.2.2.2.1,frame.2.2.2.2.1,
      fun j hj=>frame.2.2.2.2.2.1 j (by simpa using hj)⟩
  exact ⟨t,by simpa using he,state.control_frame ft.memory (fun j _ hj=>ft.tapes j (by simpa using hj))
    (RationalAccumulator.word_of_eq (ft.tapes 1257 (by decide)) state.indexWord),word,ft⟩

theorem State.reset_index {V E : Type*} {half : ℕ} {data : Gluing.Data V E half}
    {p : Plan (2*half)} {cursor index : ℕ} {s : Store} (state : State data p cursor index s)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃t,Executes input tape (WordLiteral.code 1257 0) (6*index.bits.length+11) s t ∧
      State data p cursor 0 t ∧ BinaryPrecision.Frame {1257} s.val t.val := by
  obtain ⟨t,he,word,ft⟩:=WordLiteral.executes 1257 0 input tape index.bits s state.indexWord
  exact ⟨t,by simpa using he,state.control_frame ft.memory (fun j hj _=>ft.tapes j (by simpa using hj)) word,ft⟩

theorem State.difference_count {V E : Type*} {half : ℕ} {data : Gluing.Data V E half}
    {p : Plan (2*half)} {cursor index : ℕ} {s : Store} (state : State data p cursor index s)
    (total left : ℕ) (ordered : left≤total) (input : List Bool) (tape : ℕ→Bool)
    (totalWord : Word s.val 141 total) (leftWord : Word s.val 154 left) (blank : Blank s.val 1258) :
    ∃cost t,Executes input tape (WordDifference.code 141 154 1258) cost s t ∧
      cost≤300*(total.bits.length+left.bits.length+4) ∧ State data p cursor index t ∧
      Word t.val 1258 (total-left) ∧ BinaryPrecision.Frame {0,1,2,1258} s.val t.val := by
  obtain ⟨cost,t,he,hc,word,zt,ft⟩:=WordDifference.executes 141 154 1258
    (by decide) (by decide) (by decide) input tape total left ordered s totalWord leftWord blank (scratch state.ready)
  have keep (j : ℕ) (hlo : 4≤j) (hj : j≠1258) : t.val.tapes j=s.val.tapes j:=
    ft.tapes j (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or];omega)
  have ready : GeometryArray.Ready t.val:=
    ⟨⟨zt 0 (by decide),zt 1 (by decide),zt 2 (by decide),zt 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by decide) (by decide)) state.ready.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by decide) (by decide)) state.ready.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by decide) (by decide)) state.ready.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by decide) (by decide)) state.ready.scratch.2.2.2.2.2.2.2⟩,
      RationalAccumulator.blank_of_eq (keep 7 (by decide) (by decide)) state.ready.seven,
      RationalAccumulator.blank_of_eq (keep 37 (by decide) (by decide)) state.ready.pack⟩
  obtain ⟨port,bank⟩:=state.bank
  have ts : State data p cursor index t:=by
    refine ⟨⟨port,?_⟩,ready,RationalAccumulator.blank_of_eq (keep 1249 (by decide) (by decide)) state.privateBlank,
      state.archive.frame 0 ((ArchiveFrame.of_binary ft).mono (by decide)) (by intro j _;rw [ft.memory]),
      RationalAccumulator.word_of_eq (keep 1255 (by decide) (by decide)) state.levelWord,
      RationalAccumulator.word_of_eq (keep 1253 (by decide) (by decide)) state.cursorWord,
      RationalAccumulator.word_of_eq (keep 1257 (by decide) (by decide)) state.indexWord,
      RationalAccumulator.blank_of_eq (keep 1242 (by decide) (by decide)) state.counterBlank,
      RationalAccumulator.blank_of_eq (keep 1256 (by decide) (by decide)) state.savedBlank⟩
    intro j hj
    have ne : j≠1258:=by
      simp only [ids,controls,Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
        Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    exact RationalAccumulator.word_of_eq (keep j (by have h:=ids_lower j hj;omega) ne) (bank j hj)
  exact ⟨cost,t,he,hc,ts,word,ft⟩

#print axioms State.difference_count
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
