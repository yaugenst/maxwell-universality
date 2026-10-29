import Maxwell.Cost.SourceCircuit.CompileSource
import Maxwell.Cost.SourceCircuit.ArithmeticTrace
import Maxwell.Cost.SourceCircuit.ArithmeticMarkers
import Maxwell.Cost.SourceCircuit.CompileSourceInitial

namespace Maxwell.Cost.SourceCircuit.CompileSourceTrace
open Logical Structured

theorem row_expression {n : ℕ} (rs : List (AllocationPass.Record n)) :
    ArithmeticTrace.rowExpression rs = Logical.rowExpression (rs.map ArithmeticMarkers.recordTerm) := rfl

theorem rows_expressions (S : Source.SparseSystem) (p : ℕ) :
    (ArithmeticMarkers.rows S p).map ArithmeticTrace.rowExpression =
      (Normalization.sourceRows S p).map Logical.rowExpression := by
  rw [← ArithmeticMarkers.rows_terms S p,List.map_map]
  rfl

theorem blockFlags_eq {n : ℕ} (rs : List (AllocationPass.Record n)) :
    ArithmeticTrace.blockFlags rs = ArithmeticMarkers.markerBlock rs := by cases rs <;> rfl

theorem followingFlags_eq {n : ℕ} (rs : List (List (AllocationPass.Record n))) :
    ArithmeticTrace.followingFlags rs = rs.flatMap ArithmeticMarkers.markerBlock := by
  unfold ArithmeticTrace.followingFlags
  congr 1
  funext row
  exact blockFlags_eq row

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
/-- The fully executed source compiler has exactly the established circuit,
including chronological gate bytes and every row output identifier. -/
theorem result_correct (S : Source.SparseSystem) (p : ℕ)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 1 ≤ S.nnz) (hp : 1 ≤ p)
    (roots : RootInitData S.n) (memory : ℕ → Bool) (allocated : Store)
    (ha : AllocateSource.Result S p roots memory allocated) :
    addressValue (CompileSource.result S p roots memory).next = (sourceCircuit S p).size ∧
      traceBytes (InitializeMetadata.width S.nnz p) (sourceCircuit_rational S p).code.trace =
        some (CompileSource.result S p roots memory).gates ∧
      (CompileSource.result S p roots memory).outputs =
        ((sourceCircuit S p).outputs.map Fin.val).flatMap (fixedWidth (InitializeMetadata.width S.nnz p)) ∧
      (CompileSource.result S p roots memory).leaves = [] ∧
      (CompileSource.result S p roots memory).terms = [] := by
  have hn := Source.dimension_le_nnz S hunit
  have allNonempty := ArithmeticMarkers.rows_nonempty S p hunit
  have hflat := ArithmeticMarkers.rows_flatten S p
  have hflags := ArithmeticMarkers.source_markers S p hunit
  have hexpr := rows_expressions S p
  cases hrows : ArithmeticMarkers.rows S p with
  | nil =>
    rw [hrows] at hflat
    have hl := congrArg List.length hflat
    simp only [List.flatten_nil,List.length_nil,AllocateSource.records_length] at hl
    omega
  | cons first rest =>
    cases first with
    | nil => exact False.elim (allNonempty [] (by simp [hrows]) rfl)
    | cons r rs =>
      have hr : AllocateSource.records S p = r::(rs++rest.flatten) := by
        simpa only [hrows,List.flatten_cons,List.cons_append] using hflat.symm
      have hf : ArithmeticPrelude.flags S = true::(List.replicate rs.length false++ArithmeticTrace.followingFlags rest) := by
        simpa only [ArithmeticPrelude.flags,hrows,List.flatMap_cons,ArithmeticMarkers.markerBlock,
          List.cons_append,followingFlags_eq] using hflags
      have he : ((r::rs)::rest).map ArithmeticTrace.rowExpression =
          (Normalization.sourceRows S p).map Logical.rowExpression := by simpa only [hrows] using hexpr
      have hv : ArithmeticPass.Valid (InitializeMetadata.width S.nnz p)
          ((r::rs)++rest.flatten)
          (List.replicate (r::rs).length false++ArithmeticTrace.followingFlags rest)
          (ArithmeticPrelude.data S p roots memory) := by
        rw [List.cons_append,← hr]
        apply ArithmeticPrelude.valid S p hn hm hp roots memory allocated ha
        have hlen := ArithmeticPrelude.flags_length S
        rw [hf] at hlen
        simpa only [List.length_cons,List.replicate_succ,List.cons_append,List.length_append,
          List.length_replicate] using hlen
      have next := CompileSourceInitial.initial_next S p roots memory allocated ha
      have gates := CompileSourceInitial.initial_gates S p roots memory allocated ha
      have leaves := CompileSourceInitial.initial_leaves S p roots memory allocated ha
      rw [← he] at next gates leaves
      have hc := ArithmeticTrace.stored_copied_rows_correct (r::rs) rest
        (ArithmeticPrelude.data S p roots memory) hv
        (fun row hrow => allNonempty row (by simp [hrows,hrow])) next gates leaves rfl rfl
      dsimp only at hc
      rw [he] at hc
      simpa only [CompileSource.result,hr,hf,ArithmeticPass.result,ArithmeticPass.loop,
        List.length_cons,List.replicate_succ,List.cons_append,ArithmeticPass.body,
        Bool.false_eq_true,ite_false,sourceCircuit,sourceCircuit_rational] using hc


structure Archives (S : Source.SparseSystem) (p : ℕ) (s : Store) : Prop where
  next : BankArray.Word s.val 95
    (fixedWidth (InitializeMetadata.width S.nnz p) (sourceCircuit S p).size)
  gates : ∃ bytes, traceBytes (InitializeMetadata.width S.nnz p)
    (sourceCircuit_rational S p).code.trace = some bytes ∧ s.val.tapes 97 = BitTape.atEnd bytes
  outputs : s.val.tapes 105 = BitTape.atEnd
    (((sourceCircuit S p).outputs.map Fin.val).flatMap (fixedWidth (InitializeMetadata.width S.nnz p)))
  room : (sourceCircuit S p).size < 2^InitializeMetadata.width S.nnz p

 theorem archives (S : Source.SparseSystem) (p : ℕ)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 1 ≤ S.nnz) (hp : 1 ≤ p)
    (roots : RootInitData S.n) (memory : ℕ → Bool) (allocated t : Store)
    (ha : AllocateSource.Result S p roots memory allocated)
    (ht : CompileSource.Result S p roots memory t) : Archives S p t := by
  obtain ⟨next,gates,outputs,_,_⟩ := result_correct S p hunit hm hp roots memory allocated ha
  have hn := fixedWidth_eq ht.finished.shape.nextLength next
  refine ⟨?_,⟨_,gates,ht.ready.gates⟩,?_,?_⟩
  · rw [← hn]
    exact ht.ready.next
  · rw [← outputs]
    exact ht.ready.outputs
  · rw [← next]
    exact ht.finished.room

set_option maxRecDepth 16384 in
/-- The finite source compiler produces the exact reference circuit archives
from canonical sparse input, with every intermediate tape computed at cost. -/
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost pre allocated start t roots,
      Executes (Codec.source S) tape (CompileSource.code k c) cost (Store.ofState BitRAMState.initial) t ∧
      cost ≤ ArithmeticPrelude.sourcePrice p S k c+
        CompileSource.passPrice S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory ∧
      Preparation.Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val ∧
      AllocateSource.Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory allocated ∧
      AllocationPass.Persistent pre allocated ∧ BinaryPrecision.Frame ArithmeticPrelude.work allocated.val start.val ∧
      ArithmeticPass.Persistent start t ∧
      CompileSource.Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory t ∧
      Archives S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨cost,pre,allocated,start,t,roots,et,hcost,hpre,ha,fpa,fas,fst,ht⟩ :=
    CompileSource.executes p S hp hm hb k c tape
  exact ⟨cost,pre,allocated,start,t,roots,et,hcost,hpre,ha,fpa,fas,fst,ht,
    archives S _ hp.1 (by omega) (Realization.binaryCoefficientPrecision_pos _ _ _)
      roots pre.val.memory allocated t ha ht⟩

end Maxwell.Cost.SourceCircuit.CompileSourceTrace
