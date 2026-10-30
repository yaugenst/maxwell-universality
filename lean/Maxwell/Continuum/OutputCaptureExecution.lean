import Maxwell.Continuum.OutputCaptureStep

/-! Uniform execution of the output-capture compiler. The original program
is finite code; its emitted bits are computed by its actual execution. -/
namespace Maxwell.Continuum.OutputCapture
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000

theorem steps (archive : ℕ) (body : BitRAM)
    (hp : body.code.all (avoids archive)=true)
    (input : List Bool) (tape : ℕ→Bool) {s t : BitRAMState} {cost : ℕ}
    (run : PricedSteps (body.next input tape) cost s t)
    (output accumulated : List Bool) :
    ∃ captured bits, captured≤2*cost ∧ bits.length≤cost ∧
      t.output=bits.reverse++s.output ∧
      PricedSteps ((program archive body).next input tape) captured
        (state archive output accumulated s)
        (state archive output (accumulated++bits) t) := by
  induction run generalizing accumulated with
  | refl s => exact ⟨0,[],by omega,by simp,by simp,by simpa using PricedSteps.refl _⟩
  | @step n extra s u t hn rest ih =>
    obtain ⟨a,x,ha,hx,hox,ex⟩ := step archive body hp input tape s u extra hn output accumulated
    obtain ⟨b,y,hb,hy,hoy,ey⟩ := ih (accumulated++x)
    refine ⟨a+b,x++y,by omega,by simpa only [List.length_append] using Nat.add_le_add hx hy,
      ?_,?_⟩
    · rw [hoy,hox,List.reverse_append,List.append_assoc]
    · simpa only [List.append_assoc] using ex.trans ey

def rawCode (archive : ℕ) (body : Code) : Code := .call (program archive body.compile)

def retained (archive : ℕ) (output accumulated : List Bool) (s : Store) : Store :=
  Store.ofState (state archive output accumulated s.val)

theorem raw_executes (archive : ℕ) (body : Code)
    (hp : body.compile.code.all (avoids archive)=true)
    (input : List Bool) (tape : ℕ→Bool) {cost : ℕ} {s t : Store}
    (run : Executes input tape body cost s t)
    (bits preceding : List Bool)
    (hout : t.val.output=bits.reverse++s.val.output)
    (ha : s.val.tapes archive=BitTape.atEnd preceding) :
    ∃ captured, captured≤2*cost+1 ∧ bits.length≤cost ∧
      Executes input tape (rawCode archive body) captured s
        (retained archive s.val.output (preceding++bits) t) := by
  obtain ⟨c,b,hc,hb,hbo,ex⟩ := steps archive body.compile hp input tape run.compiled_steps
    s.val.output preceding
  have hbits : b=bits := by
    have hh : b.reverse++s.val.output=bits.reverse++s.val.output := hbo.symm.trans hout
    exact List.reverse_injective (List.append_cancel_right hh)
  subst b
  rw [initial_state archive preceding s ha] at ex
  have hh : (program archive body.compile).code[
      (state archive s.val.output (preceding++bits) (t.place body.size)).pc]?=some .halt := by
    exact lookup_first archive body.compile body.size .halt body.compile_halt
  refine ⟨c+1,by omega,hb,?_⟩
  exact Executes.call (program archive body.compile) s
    (state archive s.val.output (preceding++bits) (t.place body.size)) c ex hh

#print axioms raw_executes
end Maxwell.Continuum.OutputCapture
