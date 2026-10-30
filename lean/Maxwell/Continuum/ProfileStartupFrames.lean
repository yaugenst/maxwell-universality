import Maxwell.Continuum.ProfileRuntimeStartup
import Maxwell.Continuum.ProfileEncodedTable

/-! Startup modifies only its natural metadata. The actual rational bank,
sample workspaces, saved transform and allocated buffers are preserved. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem startup_rational_frame {v : ℕ→Parts} {s t : Store} (h : Ready dftRegisters v s)
    (z : NatAssign.Scratch t.val) (f : BinaryPrecision.Frame startupWorkspace s.val t.val) :
    Ready dftRegisters v t := by
  refine ⟨?_,z⟩
  have hd : Disjoint (ids dftRegisters) startupWorkspace := by decide
  intro i hi
  exact word_of_eq (f.tapes i (fun hh => Finset.disjoint_left.mp hd hi hh)) (h.1 i hi)

theorem startup_phaseClean {s t : Store} (h : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame startupWorkspace s.val t.val) : Phase.Runtime.Clean t.val := by
  have hd : Disjoint ((PhaseMachine.Runtime.ids.erase 652).erase 653) startupWorkspace := by decide
  intro i hi
  exact blank_of_eq (f.tapes i (fun hh => Finset.disjoint_left.mp hd hi hh)) (h i hi)

theorem startup_glueClean {s t : Store} (h : Glue.Clean s.val)
    (f : BinaryPrecision.Frame startupWorkspace s.val t.val) : Glue.Clean t.val := by
  have hd : Disjoint (GlueMachine.Runtime.ids.erase 640) startupWorkspace := by decide
  intro i hi
  exact blank_of_eq (f.tapes i (fun hh => Finset.disjoint_left.mp hd hi hh)) (h i hi)

theorem startup_floorClean {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame startupWorkspace s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨blank_of_eq (f.tapes 4 (by decide)) h.1,?_⟩
  have hd : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) startupWorkspace := by decide
  intro i hi
  exact blank_of_eq (f.tapes i (fun hh => Finset.disjoint_left.mp hd hi hh)) (h.2 i hi)

theorem startup_scratch {s t : Store} (h : BankArray.Scratch s.val)
    (z : NatAssign.Scratch t.val) (f : BinaryPrecision.Frame startupWorkspace s.val t.val) :
    BankArray.Scratch t.val :=
  ⟨z 0 (by decide),z 1 (by decide),z 2 (by decide),z 3 (by decide),
    blank_of_eq (f.tapes 5 (by decide)) h.2.2.2.2.1,
    blank_of_eq (f.tapes 6 (by decide)) h.2.2.2.2.2.1,
    blank_of_eq (f.tapes 8 (by decide)) h.2.2.2.2.2.2.1,
    blank_of_eq (f.tapes 9 (by decide)) h.2.2.2.2.2.2.2⟩

theorem startup_input_frame {n : ℕ} {a : PartArray.Table n} {s t : Store} (h : a.Ready s)
    (z : NatAssign.Scratch t.val) (f : BinaryPrecision.Frame startupWorkspace s.val t.val) : a.Ready t := by
  refine ⟨startup_scratch h.scratch z f,blank_of_eq (f.tapes 7 (by decide)) h.seven,
    BankArray.word_of_eq (f.tapes 200 (by decide)) h.width,
    BankArray.word_of_eq (f.tapes 202 (by decide)) h.basePositive,
    BankArray.word_of_eq (f.tapes 203 (by decide)) h.baseNegative,
    BankArray.word_of_eq (f.tapes 204 (by decide)) h.baseDenominator,
    BankArray.word_of_eq (f.tapes 205 (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem startup_output_frame {n : ℕ} {a : PartArray.Table n} {s t : Store} (h : a.OutputReady s)
    (z : NatAssign.Scratch t.val) (f : BinaryPrecision.Frame startupWorkspace s.val t.val) : a.OutputReady t := by
  apply h.transfer f.memory _ (startup_scratch h.scratch z f) (blank_of_eq (f.tapes 7 (by decide)) h.seven)
  intro i hi
  apply f.tapes i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def producerState_after_startup {N U : ℕ} {s t : Store} (v : ℕ→Parts)
    (h : Ready dftRegisters v s) (hw : WidthBank dftRegisters (roundedWidth (profileGrid N) U) v)
    (saved : Parts) (hs : StoredParts.Stored 701 saved s.val)
    (hsw : saved.Width (roundedWidth (profileGrid N) U))
    (inner : List Bool) (hc : BankArray.Word s.val 201 inner)
    (hcl : inner.length≤roundedWidth (profileGrid N) U)
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (z : NatAssign.Scratch t.val) (f : BinaryPrecision.Frame startupWorkspace s.val t.val)
    (parameters : DFTParameters (profileDegree N) (profileWorkBits N) t)
    (power : Word t.val 144 (2^profileWorkBits N)) (grid : Word t.val 664 (profileGrid N)) :
    ProducerState (profileGrid N) (profileDegree N) (profileWorkBits N) U t :=
  ⟨v,startup_rational_frame h z f,hw,saved,
    ⟨word_of_eq (f.tapes 701 (by decide)) hs.1,word_of_eq (f.tapes 702 (by decide)) hs.2.1,
      word_of_eq (f.tapes 703 (by decide)) hs.2.2⟩,
    hsw,inner,BankArray.word_of_eq (f.tapes 201 (by decide)) hc,hcl,
    startup_phaseClean hp f,startup_glueClean hg f,startup_floorClean hf f,parameters,power,grid⟩

#print axioms producerState_after_startup
end Maxwell.Continuum.Profile.Runtime
