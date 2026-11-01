import Maxwell.Continuum.RationalDataflowArrayStorageFrame
import Maxwell.Continuum.StoredGeometryStorageFrame
import Maxwell.Continuum.StoredDecoderRowCleanup
import Maxwell.Continuum.StoredGeometryTerminal
import Maxwell.Continuum.StoredWellPayload

/-! Shared packed geometry and rational-array storage survive the decoder
row's actual reads, arithmetic, canonical serialization, and cleanup. -/
namespace Maxwell.Continuum
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem DecoderRow.scratch_frame {s t : Store} (scratch : BankArray.Scratch s.val)
    (frame : GeometryOutput.OutputFrame DecoderRow.work s.val t.val)
    (zero : NatAssign.Scratch t.val):BankArray.Scratch t.val:=
  ⟨zero 0 (by decide),zero 1 (by decide),zero 2 (by decide),zero 3 (by decide),
    blank_of_eq (frame.tapes 5 (by decide)) scratch.2.2.2.2.1,
    blank_of_eq (frame.tapes 6 (by decide)) scratch.2.2.2.2.2.1,
    blank_of_eq (frame.tapes 8 (by decide)) scratch.2.2.2.2.2.2.1,
    blank_of_eq (frame.tapes 9 (by decide)) scratch.2.2.2.2.2.2.2⟩

theorem DecoderRow.table_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (frame : GeometryOutput.OutputFrame DecoderRow.work s.val t.val)
    (zero : NatAssign.Scratch t.val):a.Ready t:=by
  apply h.storage_frame frame.memory _ (scratch_frame h.scratch frame zero)
    (blank_of_eq (frame.tapes 7 (by decide)) h.seven)
  intro i hi
  exact frame.tapes i (fun hm=>Finset.disjoint_left.mp (by decide :
    Disjoint ({200,202,203,204,205}:Finset ℕ) DecoderRow.work) hi hm)

theorem DecoderRow.geometry_frame {n base width B : ℕ} {data : Vector ℕ n}
    {clock : List Bool} {constants v : ℕ→ℕ} {s t : Store}
    (g : GeometryOutput.Context data base width B clock constants v s)
    (frame : GeometryOutput.OutputFrame DecoderRow.work s.val t.val)
    (zero : NatAssign.Scratch t.val):GeometryOutput.Context data base width B clock constants v t:=by
  apply g.storage_frame frame.memory _ (frame.tapes 962 (by decide))
    (scratch_frame g.ready.scratch frame zero) (blank_of_eq (frame.tapes 7 (by decide)) g.ready.seven)
  intro i hi
  exact frame.tapes i (fun hm=>Finset.disjoint_left.mp (by decide :
    Disjoint GeometryOutput.ids DecoderRow.work) hi hm)

#print axioms DecoderRow.geometry_frame
end Maxwell.Continuum
