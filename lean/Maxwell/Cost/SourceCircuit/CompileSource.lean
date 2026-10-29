import Maxwell.Cost.SourceCircuit.ArithmeticPrelude
import Maxwell.Cost.SourceCircuit.ArithmeticBounds

namespace Maxwell.Cost.SourceCircuit.CompileSource
open Structured

def code (k c : ℕ) : Code := .seq (ArithmeticPrelude.sourceCode k c) ArithmeticPass.code

def result (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) : ArithmeticPass.Data :=
  match AllocateSource.records S p, ArithmeticPrelude.flags S with
  | r::rs, _::fs => ArithmeticPass.result r rs fs (ArithmeticPrelude.data S p roots memory)
  | _, _ => ArithmeticPrelude.data S p roots memory

def passPrice (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) : ℕ :=
  match AllocateSource.records S p, ArithmeticPrelude.flags S with
  | r::rs, _::fs => ArithmeticPass.costBound p (InitializeMetadata.width S.nnz p)
      S.nnz.bits.length r rs fs (ArithmeticPrelude.data S p roots memory)
  | _, _ => 0

structure Result (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) (s : Store) : Prop where
  ready : ArithmeticPass.Ready (AllocateSource.clock S p) p (result S p roots memory) s
  finished : ArithmeticPass.Finished (InitializeMetadata.width S.nnz p) (result S p roots memory)
  archive : s.val.tapes 85 = NormalizedRecordParser.cursor (Preparation.archive S p)
    (Preparation.archive S p).length
  leaves : s.val.tapes 98 = Increment.cursor (ArithmeticPrelude.leafWords S p).flatten [] 0
  markers : s.val.tapes 24 = Increment.cursor (ArithmeticPrelude.flags S) [] 0
  counter : ∃ co : ℤ, ∃ xs : List Bool, s.val.tapes 100 = BitTape.shifted xs co ∧ xs.length = S.nnz.bits.length

set_option maxRecDepth 16384 in
theorem step (S : Source.SparseSystem) (p : ℕ) (hm : 1 ≤ S.nnz)
    (input : List Bool) (tape : ℕ → Bool) (roots : RootInitData S.n)
    (memory : ℕ → Bool) (s : Store) (h : ArithmeticPrelude.Result S p roots memory s) :
    ∃ cost t, Executes input tape ArithmeticPass.code cost s t ∧
      cost ≤ passPrice S p roots memory ∧ Result S p roots memory t ∧ ArithmeticPass.Persistent s t := by
  have hlength := AllocateSource.records_length S p
  have hflags := ArithmeticPrelude.flags_length S
  cases hrs : AllocateSource.records S p with
  | nil => rw [hrs] at hlength; simp at hlength; omega
  | cons r rs =>
    cases hfs : ArithmeticPrelude.flags S with
    | nil => rw [hfs] at hflags; simp at hflags; omega
    | cons marker fs =>
      have hv : ArithmeticPass.Valid (InitializeMetadata.width S.nnz p) (r::rs) (false::fs)
          (ArithmeticPrelude.data S p roots memory) := by
        rw [← hrs]
        apply h.room
        simpa [hfs] using hflags
      obtain ⟨co,h100⟩ := h.counter
      obtain ⟨cost,t,xs,hcost,he,ht,hfinish,t100,hlen,t85,t98,t24,hframe⟩ :=
        ArithmeticPass.executes input tape (AllocateSource.clock S p) p (InitializeMetadata.width S.nnz p)
          r rs marker fs (ArithmeticPrelude.data S p roots memory) [] [] [] [] [] [] S.nnz.bits co s
          (AllocateSource.clock_length S p)
          (by intro q hq; apply AllocateSource.records_precision S p q; simpa only [hrs] using hq)
          h.ready hv (by rw [addressValue_bits]; simpa [hrs] using hlength.symm) h100
          (by simpa [hfs] using h.markers)
          (by simpa [← hrs,AllocateSource.records_wire] using h.archive)
          (by simpa using h.leaves)
      refine ⟨cost,t,he,by simpa [passPrice,hrs,hfs] using hcost,
        ⟨?_,?_,?_,?_,?_,⟨co,xs,t100,hlen⟩⟩,hframe⟩
      · simpa only [result,hrs,hfs] using ht
      · simpa only [result,hrs,hfs] using hfinish
      · simpa only [← hrs,AllocateSource.records_wire,List.nil_append,List.append_nil,
          List.length_nil,Nat.cast_zero,zero_add] using t85
      · simpa only [ArithmeticPrelude.data,List.nil_append,List.append_nil] using t98
      · simpa only [← hfs,List.nil_append,List.append_nil] using t24

set_option maxRecDepth 16384 in
/-- One uniform finite program computes the actual source circuit gate and
row-output archives from canonical sparse coefficients alone. -/
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost pre allocated start t roots,
      Executes (Codec.source S) tape (code k c) cost (Store.ofState BitRAMState.initial) t ∧
      cost ≤ ArithmeticPrelude.sourcePrice p S k c+
        passPrice S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory ∧
      Preparation.Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val ∧
      AllocateSource.Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory allocated ∧
      AllocationPass.Persistent pre allocated ∧ BinaryPrecision.Frame ArithmeticPrelude.work allocated.val start.val ∧
      ArithmeticPass.Persistent start t ∧ Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory t := by
  obtain ⟨pc,pre,allocated,start,roots,ep,hpc,hpre,ha,fpa,fas,hs⟩ :=
    ArithmeticPrelude.source_executes p S hp hm hb k c tape
  obtain ⟨ac,t,ea,hac,ht,fst⟩ := step S (Realization.binaryCoefficientPrecision S.nnz k c)
    (by omega) (Codec.source S) tape roots pre.val.memory start hs
  exact ⟨pc+ac,pre,allocated,start,t,roots,ep.seq ea,Nat.add_le_add hpc hac,hpre,ha,fpa,fas,fst,ht⟩

end Maxwell.Cost.SourceCircuit.CompileSource
