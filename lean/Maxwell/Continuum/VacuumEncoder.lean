import Maxwell.Continuum.Main
import Maxwell.Cost.EmitRows
import Maxwell.Cost.DecoderParser.ReadFields

namespace Maxwell.Continuum.VacuumEncoder
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 4096

def header : List Bool := Codec.nat 0++Codec.nat 0++Codec.nat 0
def row : List Bool := Codec.rat 0++Codec.nat 0
def emitCode : Code := .seq (EmitLiteral.code 30 [false]) (EmitRows.code header row)
def code : Code := .seq (DecoderParser.readNatural 19) emitCode
def program : BitRAM := code.compile
def fuel (n : ℕ) : ℕ := 21*n.bits.length+16+5+EmitRows.bound header row n+1

theorem description_eq (S : Source.SparseSystem) :
    Cost.FiniteDecoder.description (Realization.vacuumDecoder S)=EmitRows.bits header row S.n := by
  rw [Cost.FiniteDecoder.description_rows]
  simp [Cost.FiniteDecoder.beforeRows,Cost.FiniteDecoder.headerData,DecoderParser.wire,
    DecoderParser.rows,DecoderParser.rowTerms,Realization.vacuumDecoder,
    EmitRows.bits,header,row,List.append_assoc]
  simp [List.flatMap_def,DecoderParser.rowWire]

theorem emit_executes (n : ℕ) (dimensionOrigin counterOrigin : ℤ)
    (input : List Bool) (randomTape : ℕ→Bool) (s : Store)
    (hn : s.val.tapes 19=BitTape.shifted n.bits dimensionOrigin)
    (hc : s.val.tapes 90={BitTape.blank with head:=counterOrigin}) :
    ∃ cost t, Executes input randomTape emitCode cost s t ∧
      cost≤5+EmitRows.bound header row n ∧
      t.val.output=(false::EmitRows.bits header row n).reverse++s.val.output ∧
      t.val.randomCursor=s.val.randomCursor := by
  let a := EmitLiteral.finish 30 [false] s
  have ea := EmitLiteral.executes 30 [false] input randomTape s
  have fa := EmitLiteral.finish_frame 30 [false] s
  obtain ⟨cost,t,he,hcost,ho,hr⟩ := EmitRows.executes header row n dimensionOrigin counterOrigin
    input randomTape a ((congrFun fa.2.2.2.2.1 19).trans hn)
      ((congrFun fa.2.2.2.2.1 90).trans hc)
  refine ⟨5+cost,t,ea.seq he,by omega,?_,hr.trans fa.2.2.2.1⟩
  rw [ho,EmitLiteral.finish_output]
  simp [List.append_assoc]

theorem encodes (S : Source.SparseSystem) :
    Realization.Encodes program S (Fin.elim0 : Fin 0→Bool) (Realization.vacuumBytes S) (fuel S.n) := by
  let suffix := Codec.list (Codec.sourceEntry S) (Codec.sourceEntries S).attach++Codec.vector S.source
  have hi : []++(Codec.nat S.n++suffix)=Codec.source S := by
    simp [suffix,Codec.source,List.append_assoc]
  obtain ⟨s,es,_,hs19,_,hsf⟩ := DecoderParser.readNatural_steps 19 (by decide) S.n [] suffix
    (Realization.randomTape (Fin.elim0 : Fin 0→Bool)) (Store.ofState BitRAMState.initial) rfl rfl rfl
  rw [hi] at es
  obtain ⟨cost,t,he,hc,ho,hr⟩ := emit_executes S.n 0 0 (Codec.source S)
    (Realization.randomTape (Fin.elim0 : Fin 0→Bool)) s
      (by simpa [BitTape.shifted,BitTape.ofList] using hs19) (hsf.tapes 90 (by decide))
  have hrun := (es.seq he).compiled_run (fuel S.n) (by unfold fuel;omega)
  refine ⟨t.place code.size,hrun.1,?_,hr.trans hsf.randomCursor⟩
  change t.val.output.reverse=_
  rw [ho,hsf.output]
  simp only [Store.ofState,BitRAMState.initial,List.append_nil,List.reverse_reverse,
    Realization.vacuumBytes,description_eq]

theorem fuel_le (n m : ℕ) (hn : n≤m) : fuel n≤(m+1)*(100*m.bits.length+160) := by
  have hbits : n.bits.length≤m.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hn
  have hh : header.length=3 := by decide +kernel
  have hr : row.length=6 := by decide +kernel
  unfold fuel EmitRows.bound
  rw [hh,hr]
  nlinarith

#print axioms encodes
#print axioms fuel_le

end Maxwell.Continuum.VacuumEncoder
