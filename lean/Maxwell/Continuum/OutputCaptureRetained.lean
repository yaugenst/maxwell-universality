import Maxwell.Continuum.OutputCaptureExecution
import Maxwell.Continuum.OutputCaptureFootprint
import Maxwell.Cost.BankArray.Common

/-! Retained payloads from actual fixed producers. Capture runs the original
computation and rewinds the computed word, with no output-data literal. -/
namespace Maxwell.Continuum.OutputCapture
open Maxwell.Cost Maxwell.Cost.Structured

def code (archive : ℕ) (body : Code) : Code :=
  .seq (rawCode archive body) (.call (Rewind.program archive))

def Frame (archive : ℕ) (original captured : Store) : Prop :=
  captured.val.address=original.val.address ∧
  captured.val.inputHead=original.val.inputHead ∧
  captured.val.memory=original.val.memory ∧
  captured.val.randomCursor=original.val.randomCursor ∧
  (∀i,i≠archive→captured.val.tapes i=original.val.tapes i)

theorem executes (archive : ℕ) (body : Code) (hp : avoidsCode archive body=true)
    (input : List Bool) (tape : ℕ→Bool) {cost : ℕ} {s t : Store}
    (run : Executes input tape body cost s t) (bits : List Bool)
    (hout : t.val.output=bits.reverse++s.val.output)
    (ha : s.val.tapes archive=BitTape.blank) :
    ∃ captured u, captured≤6*cost+7 ∧ bits.length≤cost ∧
      Executes input tape (code archive body) captured s u ∧
      BankArray.Word u.val archive bits ∧ u.val.output=s.val.output ∧
      Frame archive t u := by
  obtain ⟨c,hc,hb,ex⟩ := raw_executes archive body (by rw [compile_avoids];exact hp)
    input tape run bits [] hout (by simpa only [BitTape.atEnd_nil] using ha)
  let v := retained archive s.val.output bits t
  have hv : v.val.tapes archive=BitTape.atEnd bits := by simp [v,retained,state,Store.ofState]
  have hr := Rewind.atEnd_steps archive input tape bits v.val v.property hv
  let u := Store.ofState (Rewind.finish archive v.val)
  have er : Executes input tape (.call (Rewind.program archive)) (4*bits.length+6) v u :=
    Executes.call _ _ _ _ hr (by simp [Rewind.program,Rewind.finish])
  refine ⟨c+(4*bits.length+6),u,by omega,hb,?_,?_,rfl,?_⟩
  · exact ex.seq er
  · refine ⟨0,?_⟩
    have hh := Rewind.finish_tape archive bits v.val hv
    simpa only [u,Store.ofState,BitTape.shifted_zero] using hh
  · refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro i hi
    simp [u,v,Store.ofState,Rewind.finish,retained,state,hi]

theorem compiled_run (archive : ℕ) (body : Code) (hp : avoidsCode archive body=true)
    (input : List Bool) (tape : ℕ→Bool) {cost : ℕ} {s t : Store}
    (run : Executes input tape body cost s t) (bits : List Bool)
    (hout : t.val.output=bits.reverse++s.val.output)
    (ha : s.val.tapes archive=BitTape.blank) :
    ∃u,
      (runPriced ((code archive body).compile.next input tape) (6*cost+8) s.val).finished=
        some (u.place (code archive body).size) ∧
      (runPriced ((code archive body).compile.next input tape) (6*cost+8) s.val).instructions≤6*cost+7 ∧
      BankArray.Word u.val archive bits ∧ u.val.output=s.val.output ∧ Frame archive t u := by
  obtain ⟨c,u,hc,_,ex,hw,ho,hf⟩ := executes archive body hp input tape run bits hout ha
  obtain ⟨hr,hsteps⟩ := ex.compiled_run (6*cost+8) (by omega)
  exact ⟨u,hr,hsteps ▸ hc,hw,ho,hf⟩

#print axioms compiled_run
end Maxwell.Continuum.OutputCapture
