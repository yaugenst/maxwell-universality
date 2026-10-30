import Maxwell.Continuum.ProfileGeneratedBits
import Maxwell.Continuum.OutputCaptureDataflow

/-! The literal radial-profile producer supplies the retained word used by
every well record. Neither the coefficients nor the resulting bits are an
input to this fixed program. The computed site count on988 is preserved. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 6500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget producerEmitCost

def retainedPayloadCode : Code := OutputCapture.code 991 generatedBitsCode

theorem generatedBits_avoids991 : OutputCapture.avoidsCode 991 generatedBitsCode=true := by decide
theorem generatedBits_preserves988 : generatedBitsCode.protectsTape 988=true := by decide
theorem generatedBits_preserves992 : generatedBitsCode.protectsTape 992=true := by decide

theorem retainedPayload_executes (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
    (v : ℕ→Parts) (hv : WidthBank dftRegisters (roundedWidth (profileGrid N) (producerSize N)) v)
    (saved : Parts) (hsv : saved.Width (roundedWidth (profileGrid N) (producerSize N)))
    (input : List Bool) (tape : ℕ→Bool) (inner oldWord : List Bool)
    (hlen : inner.length≤roundedWidth (profileGrid N) (producerSize N)) (s : Store)
    (hd : NatAssign.Bank dimensionIds (initialDimensions N) s.val)
    (hb : NatAssign.Bank allocationIds (bufferInput N 0 heap) s.val)
    (hz : ∀i∈startupBlanks,Blank s.val i) (hr : Ready dftRegisters v s)
    (hs : StoredParts.Stored 701 saved s.val) (hinner : BankArray.Word s.val 201 inner)
    (hcount : BankArray.Word s.val 700 oldWord)
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (harray : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h205 : Blank s.val 205) (h215 : Blank s.val 215) (h216 : Blank s.val 216)
    (hserial : ∀i∈serializerPorts,Blank s.val i) (h991 : s.val.tapes 991=BitTape.blank) :
    ∃cost t values,Executes input tape retainedPayloadCode cost s t ∧
      cost≤6*producerEmitCost N oldWord.length+7 ∧
      BankArray.Word t.val 991 (profileBits N) ∧ t.val.output=s.val.output ∧
      Ready StoredInteger.slots values t ∧
      WidthBank StoredInteger.slots (StoredDyadic.registerWidth (profileWorkBits N)
        (encodedTableWidth (profileDegree N) (runtimeBudget N))) values ∧
      Word t.val 144 (2^profileWorkBits N) ∧ DyadicFloor.Clean t.val ∧
      (∀i∈({201,726,727,728}:Finset ℕ),Blank t.val i) ∧
      t.val.tapes 988=s.val.tapes 988 ∧ t.val.tapes 992=s.val.tapes 992 := by
  obtain ⟨c,u,values,ex,hc,ho,hr,hw,hp,hf,hz⟩ := generatedBits_executes N heap hh v hv saved hsv
    input tape inner oldWord hlen s hd hb hz hr hs hinner hcount hp hg hf harray h7 h37
    h205 h215 h216 hserial
  obtain ⟨d,t,hd,_,et,word,out,frame⟩ := OutputCapture.executes 991 generatedBitsCode
    generatedBits_avoids991 input tape ex (profileBits N) ho h991
  refine ⟨d,t,values,et,by omega,word,out,frame.ready (by decide) hr,hw,
    frame.word 144 _ (by decide) hp,frame.floor_clean (by decide) hf,?_,?_,?_⟩
  · intro i hi
    exact frame.blank i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega) (hz i hi)
  · exact (frame.tapes 988 (by decide)).trans (ex.protectsTape 988 generatedBits_preserves988)
  · exact (frame.tapes 992 (by decide)).trans (ex.protectsTape 992 generatedBits_preserves992)

#print axioms retainedPayload_executes
end Maxwell.Continuum.Profile.Runtime
