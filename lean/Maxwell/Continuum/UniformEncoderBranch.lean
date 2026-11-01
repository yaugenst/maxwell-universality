import Maxwell.Continuum.VacuumEncoder
import Maxwell.Cost.MagnitudeMax.Branch
import Maxwell.Cost.Structured.Prefix

/-! A uniform encoder selects its case from the actual source parser.
The computed continuation receives exactly the parser state used in its
checked execution, while the vacuum branch emits its entire description. -/
noncomputable section
namespace Maxwell.Continuum.UniformEncoder
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def code (computed : Code) : Code := .seq MagnitudeMax.Branch.code
  (.branch 1004 VacuumEncoder.emitCode computed)
def program (computed : Code) : BitRAM := (code computed).compile
def vacuumFuel (p : Source.Parameters) (S : Source.SparseSystem) : ℕ :=
  MagnitudeMax.Branch.price S (MagnitudeMax.inputWidth p S)+
    1+5+EmitRows.bound VacuumEncoder.header VacuumEncoder.row S.n+1

theorem vacuum_encodes (computed : Code) (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hbase : S.source=0∨S.nnz≤1) :
    Realization.Encodes (program computed) S (Fin.elim0 : Fin 0→Bool)
      (Realization.vacuumBytes S) (vacuumFuel p S) := by
  let tape:=Realization.randomTape (Fin.elim0 : Fin 0→Bool)
  obtain ⟨c,s,hc,es,_,_,_,_,_,_,_,dim,_,_,_,_,_,random,output,_,fresh,_⟩:=
    MagnitudeMax.Branch.executes_record (Codec.sourceRecord S) (MagnitudeMax.inputWidth p S)
      (MagnitudeMax.inputWidth_pos p S) (MagnitudeMax.promised_entry_width p S hp)
      (MagnitudeMax.promised_rhs_width p S hp) [] tape
  rw [ParseSource.source_wire,List.append_nil] at es
  have flag : s.val.registers 1004=true := by
    rw [MagnitudeMax.Branch.branch_condition p S hp tape c s es]
    exact decide_eq_true hbase
  obtain ⟨d,t,et,hd,bytes,random'⟩:=VacuumEncoder.emit_executes S.n 0 0 (Codec.source S) tape s
    (by simpa [Codec.sourceRecord,BitTape.ofList,BitTape.shifted] using dim)
    (fresh 90 (by decide +kernel))
  have execution : Executes (Codec.source S) tape (code computed) (c+(1+d))
      (Store.ofState BitRAMState.initial) t:=es.seq (.yes flag et)
  have run:=execution.compiled_run (vacuumFuel p S) (by
    change c≤MagnitudeMax.Branch.price S (MagnitudeMax.inputWidth p S) at hc
    unfold vacuumFuel
    omega)
  refine ⟨t.place (code computed).size,run.1,?_,random'.trans random⟩
  change t.val.output.reverse=Realization.vacuumBytes S
  rw [bytes,output,List.append_nil,List.reverse_reverse]
  rw [Realization.vacuumBytes,VacuumEncoder.description_eq]

theorem computed_executes (p : Source.Parameters) (S : Source.SparseSystem) (hp : Source.Promises p S)
    (hm : 2≤S.nnz) (hb : S.source≠0) (original computed : Code)
    (start : Code.Prefix MagnitudeMax.Branch.code original computed)
    (tape : ℕ→Bool) (cost : ℕ) (t : Store)
    (run : Executes (Codec.source S) tape original cost (Store.ofState BitRAMState.initial) t) :
    Executes (Codec.source S) tape (code computed) (cost+1) (Store.ofState BitRAMState.initial) t := by
  obtain ⟨a,b,s,eq,parse,rest⟩:=start.split run
  have flag : s.val.registers 1004=false := by
    rw [MagnitudeMax.Branch.branch_condition p S hp tape a s parse]
    exact decide_eq_false (not_or.mpr ⟨hb,by omega⟩)
  have execution:=parse.seq (Executes.no (yes:=VacuumEncoder.emitCode) flag rest)
  have costs : cost+1=a+(1+b) := by omega
  rw [costs]
  exact execution

#print axioms vacuum_encodes
#print axioms computed_executes
end Maxwell.Continuum.UniformEncoder
