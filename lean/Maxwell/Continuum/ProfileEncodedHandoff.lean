import Maxwell.Continuum.ProfileEncodedTable
import Maxwell.Continuum.CutoffGeneratedCoefficients

/-! The actual computed profile rows become the ordinary input table for
the cutoff cache by five charged metadata exchanges. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
attribute [local irreducible] profileDegree encodedCoefficient

theorem EncodedTableResult.coefficients {N W : ℕ} {a : Table (profileDegree N)} {s : Store}
    (r : EncodedTableResult N W a s) :
    (∀k,(r.table.getD k).Valid) ∧
    (∀k<profileDegree N,(r.table.getD k).Width (encodedTableWidth (profileDegree N) W)) ∧
    (∀k<profileDegree N,(r.table.getD k).value=(Calibration.RawCutoff.coefficient N k).value) := by
  refine ⟨?_,?_,?_⟩
  · intro k
    by_cases hk : k<profileDegree N
    · simpa only [Table.getD,dite_eq_left hk] using (r.correct ⟨k,hk⟩).1
    · simp only [Table.getD,dite_eq_right hk]
      exact Parts.literal_valid _
  · intro k hk
    simpa only [Table.getD,dite_eq_left hk] using (r.correct ⟨k,hk⟩).2.1
  · intro k hk
    simp only [Table.getD,dite_eq_left hk]
    rw [(r.correct ⟨k,hk⟩).2.2,Calibration.RawCutoff.coefficient_value]

theorem EncodedTableResult.input_executes {N W : ℕ} {a : Table (profileDegree N)} {s : Store}
    (r : EncodedTableResult N W a s)
    (hm : a.MetadataWidth (encodedTableWidth (profileDegree N) W))
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape headerSwapCode cost s t ∧
      cost≤256*(encodedTableWidth (profileDegree N) W+1) ∧
      SharedConversion.Ready dftRegisters r.values t ∧ r.table.Ready t ∧ r.input.OutputReady t ∧
      Blank t.val 216 ∧ BankArray.Word t.val 201 r.countWord ∧
      BinaryPrecision.Frame (insert 216 headerSlots) s.val t.val := by
  have hW : W≤encodedTableWidth (profileDegree N) W := by
    unfold encodedTableWidth correctionWorkingWidth endpointWorkingWidth
    omega
  obtain ⟨cost,t,e,hc,_,at',bt,blank,frame⟩ := headerSwap_executes r.input r.table
    (encodedTableWidth (profileDegree N) W) (r.inputMetadata.mono hW)
    (tableMetadata_width r.metadata hm) dftRegisters r.values input tape s r.ready.rational
    r.inputReady r.output r.swapBlank
  exact ⟨cost,t,e,hc,sharedReady_headerSwap r.ready frame,at',bt,blank,
    BankArray.word_of_eq (frame.tapes 201 (by decide)) r.count,frame⟩

#print axioms EncodedTableResult.coefficients
#print axioms EncodedTableResult.input_executes
end Maxwell.Continuum.Profile.Runtime
