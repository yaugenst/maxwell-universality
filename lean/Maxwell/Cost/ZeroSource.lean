import Maxwell.Cost.ZeroSource.Emit
import Maxwell.Cost.DecoderParser.ReadFields
import Maxwell.Realization.ZeroSource

set_option maxRecDepth 4096

namespace Maxwell.Cost.ZeroSource
open Structured

/-- A fixed fallback encoder for an exactly zero right-hand side. The caller
must establish that branch condition; the program emits n zero readout rows. -/
def code : Code := .seq (DecoderParser.readNatural 19) emitCode

def encoder : BitRAM := code.compile

def fuel (n : ℕ) : ℕ := 21*n.bits.length+16+emitBound n+1

theorem encodes (S : Source.SparseSystem) (draw : Realization.Draw 0) :
    Realization.Encodes encoder S draw (fuel S.n) (BaseCases.zeroInstance S) := by
  let suffix := Codec.list (Codec.sourceEntry S) (Codec.sourceEntries S).attach ++ Codec.vector S.source
  have hi : [] ++ (Codec.nat S.n ++ suffix) = Codec.source S := by
    simp [suffix, Codec.source, List.append_assoc]
  obtain ⟨parsed, ep, hphead, hp19, hp10, hpf⟩ :=
    DecoderParser.readNatural_steps 19 (by decide) S.n [] suffix (Realization.randomTape draw)
      (Store.ofState BitRAMState.initial) rfl rfl rfl
  rw [hi] at ep
  have h19 : parsed.val.tapes 19 = BitTape.shifted S.n.bits 0 := by
    simpa [BitTape.shifted, BitTape.ofList] using hp19
  have h90 : parsed.val.tapes 90 = {BitTape.blank with head := (0:ℤ)} := by
    exact hpf.tapes 90 (by decide)
  obtain ⟨cost, t, et, hcost, hout, hrandom⟩ := emit_steps S.n 0 0 (Codec.source S)
    (Realization.randomTape draw) parsed h19 h90
  have he : Executes (Codec.source S) (Realization.randomTape draw) code
      (21*S.n.bits.length+16+cost) (Store.ofState BitRAMState.initial) t := ep.seq et
  have hr := he.compiled_run (fuel S.n) (by unfold fuel; omega)
  refine ⟨t.place code.size, hr.1, ?_, ?_⟩
  · have ho : parsed.val.output = [] := hpf.output
    change t.val.output.reverse = _
    rw [hout, ho, List.append_nil, List.reverse_reverse, targetBits_eq]
  · exact hrandom.trans hpf.randomCursor

theorem header_length : header.length = 66 := by decide +kernel

theorem row_length : row.length = 6 := by decide +kernel

/-- All written rows and their countdown arithmetic are charged linearly
in the input dimension and its binary width. -/
theorem fuel_le (n m : ℕ) (hn : n ≤ m) :
    fuel n ≤ (m+1)*(100*m.bits.length+410) := by
  have hbits : n.bits.length ≤ m.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hn
  unfold fuel emitBound
  rw [header_length, row_length]
  nlinarith

theorem source_fuel_le (S : Source.SparseSystem) (hunit : IsUnit (Source.realMatrix S)) :
    fuel S.n ≤ (S.nnz+1)*(100*S.nnz.bits.length+410) :=
  fuel_le S.n S.nnz (Source.dimension_le_nnz S hunit)

/-- Concrete zero-RHS branch: full target resources and universal recovery
are independent of the arbitrary number of original source coordinates. -/
theorem zero_rhs_branch (p : Source.Parameters) (C : Realization.Constants)
    (S : Source.SparseSystem) (hb : S.source = 0)
    (hsize : 4 ≤ Realization.sizeBudget C S) (hbits : 2 ≤ Realization.bitBudget C S) :
    (∀ draw : Realization.Draw 0,
      Realization.Encodes encoder S draw (fuel S.n) (BaseCases.zeroInstance S)) ∧
    Realization.Resources C S (BaseCases.zeroInstance S) ∧
    Realization.GoodDraw p C S (BaseCases.zeroInstance S) :=
  ⟨encodes S, Realization.zero_source_resources C S hsize hbits,
    Realization.zero_source_goodDraw p C S hb⟩

end Maxwell.Cost.ZeroSource
