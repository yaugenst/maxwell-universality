import Maxwell.Continuum.ProfileCorrectionExecution
import Maxwell.Continuum.RationalDataflowNaturalChannels

/-! The correction pass reads its index and dyadic denominator from the
actual runtime words, while retaining the computed endpoint moments. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def correctionSetup : List Instruction := [.literal 7 1,.literal 8 0,.literal 6 1]
def correctionSetupValues (v : ℕ→Parts) : ℕ→Parts := evaluate correctionSetup v
def correctionIndexValues (n : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (correctionSetupValues v) 8 ⟨n,0,1⟩
def correctionInitialValues (n P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (correctionIndexValues n v) 6 ⟨1,0,2^P⟩
def correctionInitializeCode : Code := .seq (program correctionSetup)
  (.seq (NaturalChannel.code .positive 201 8) (NaturalChannel.code .denominator 144 6))

theorem correctionSetup_valid : ∀a∈correctionSetup,a.Valid dftRegisters := by
  simp only [correctionSetup,List.mem_cons,List.not_mem_nil,or_false]
  intro a ha
  rcases ha with rfl|rfl|rfl <;> simp [Instruction.Valid,dftRegisters]

theorem correctionSetup_trace (v : ℕ→Parts) (B : ℕ) (hB : 1≤B)
    (hw : WidthBank dftRegisters B v) : WidthTrace dftRegisters B correctionSetup v := by
  have h0 : (Parts.literal 0).Width B := (show (Parts.literal 0).Width 1 by simp [Parts.Width,Parts.literal]).mono hB
  have h1 : (Parts.literal 1).Width B := (show (Parts.literal 1).Width 1 by simp [Parts.Width,Parts.literal]).mono hB
  exact ⟨hw,h1,hw.update 7 h1,h0,(hw.update 7 h1).update 8 h0,h1,
    ((hw.update 7 h1).update 8 h0).update 6 h1⟩

theorem correctionInitialValues_constants (n P : ℕ) (v : ℕ→Parts) :
    correctionInitialValues n P v 0=v 0 ∧ correctionInitialValues n P v 3=v 3 ∧
    correctionInitialValues n P v 7=Parts.literal 1 ∧
    correctionInitialValues n P v 8=⟨n,0,1⟩ ∧
    correctionInitialValues n P v 6=⟨1,0,2^P⟩ := by
  simp [correctionInitialValues,correctionIndexValues,correctionSetupValues,correctionSetup,evaluate,Instruction.update]

theorem correctionInitialValues_width (n P B : ℕ) (v : ℕ→Parts) (hB : 1≤B)
    (hn : n.bits.length≤B) (hp : (2^P).bits.length≤B) (hw : WidthBank dftRegisters B v) :
    WidthBank dftRegisters B (correctionInitialValues n P v) := by
  have base : WidthBank dftRegisters B (correctionSetupValues v) := by
    have h0 : (Parts.literal 0).Width B := (show (Parts.literal 0).Width 1 by simp [Parts.Width,Parts.literal]).mono hB
    have h1 : (Parts.literal 1).Width B := (show (Parts.literal 1).Width 1 by simp [Parts.Width,Parts.literal]).mono hB
    exact ((hw.update 7 h1).update 8 h0).update 6 h1
  exact (base.update 8 ⟨hn,by simp,by simpa using hB⟩).update 6
    ⟨by simpa using hB,by simp,hp⟩

theorem correctionInitialValues_good (n P : ℕ) (v : ℕ→Parts) (hv : Good dftRegisters v) :
    Good dftRegisters (correctionInitialValues n P v) := by
  have base : Good dftRegisters (correctionSetupValues v) :=
    ((hv.update 7 (Parts.literal_valid 1)).update 8 (Parts.literal_valid 0)).update 6 (Parts.literal_valid 1)
  exact (base.update 8 (x := ⟨n,0,1⟩) Nat.zero_lt_one).update 6
    (x := ⟨1,0,2^P⟩) (by change 0<2^P;positivity)

theorem correction_initialize_executes (n P B : ℕ) (v : ℕ→Parts) (hB : 1≤B)
    (hw : WidthBank dftRegisters B v) (xs : List Bool) (hn : addressValue xs=n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready dftRegisters v s)
    (hc : BankArray.Word s.val 201 xs) (hp : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape correctionInitializeCode cost s t ∧
      cost≤3*operationCost B+31*xs.length+31*(2^P).bits.length+85 ∧
      Ready dftRegisters (correctionInitialValues n P v) t ∧
      BinaryPrecision.Frame (workspace dftRegisters) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,r0,f0⟩ := program_executes dftRegisters correctionSetup correctionSetup_valid v B
    (correctionSetup_trace v B hB hw) input tape s hs
  obtain ⟨c1,s1,e1,h1,r1,f1⟩ := NaturalChannel.executes dftRegisters .positive 201 8
    (by decide) (by decide) (correctionSetupValues v) xs input tape s0 r0
    (BankArray.word_of_eq (f0.tapes 201 (outside_workspace _ _ (by decide))) hc)
  have eindex : Function.update (correctionSetupValues v) 8
      (NaturalChannel.replace .positive (correctionSetupValues v 8) (addressValue xs))=correctionIndexValues n v := by
    rw [hn]
    simp [correctionSetupValues,correctionSetup,evaluate,Instruction.update,correctionIndexValues,NaturalChannel.replace,Parts.literal]
  rw [eindex] at r1
  have f1a : BinaryPrecision.Frame (workspace dftRegisters) s0.val s1.val := f1.mono (by
    intro i hi
    have he : i=positivePort 8 := by simpa only [NaturalChannel.port,Finset.mem_singleton] using hi
    subst i
    exact Finset.mem_union_right _ (NaturalChannel.port_mem .positive dftRegisters 8 (by decide)))
  have f01 := f0.trans f1a
  obtain ⟨c2,t,e2,h2,r2,f2⟩ := NaturalChannel.executes dftRegisters .denominator 144 6
    (by decide) (by decide) (correctionIndexValues n v) ((2:ℕ)^P).bits input tape s1 r1
    (by
      obtain ⟨origin,ho⟩ := hp
      exact ⟨origin,(f01.tapes 144 (outside_workspace _ _ (by decide))).trans ho⟩)
  have escale : Function.update (correctionIndexValues n v) 6
      (NaturalChannel.replace .denominator (correctionIndexValues n v 6) (addressValue (2^P).bits))=
        correctionInitialValues n P v := by
    rw [addressValue_bits]
    simp [correctionInitialValues,correctionIndexValues,correctionSetupValues,correctionSetup,
      evaluate,Instruction.update,NaturalChannel.replace,Parts.literal]
  rw [escale] at r2
  have f2a : BinaryPrecision.Frame (workspace dftRegisters) s1.val t.val := f2.mono (by
    intro i hi
    have he : i=denominatorPort 6 := by simpa only [NaturalChannel.port,Finset.mem_singleton] using hi
    subst i
    exact Finset.mem_union_right _ (NaturalChannel.port_mem .denominator dftRegisters 6 (by decide)))
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,r2,f01.trans f2a⟩
  simp only [correctionSetup,List.length_cons,List.length_nil] at h0
  have oldPositive : dataValues (correctionSetupValues v) (NaturalChannel.port .positive 8)=0 := by
    simp [NaturalChannel.port,dataValues_positive,correctionSetupValues,correctionSetup,evaluate,Instruction.update,Parts.literal]
  have oldDenominator : dataValues (correctionIndexValues n v) (NaturalChannel.port .denominator 6)=1 := by
    simp [NaturalChannel.port,dataValues_denominator,correctionIndexValues,correctionSetupValues,
      correctionSetup,evaluate,Instruction.update,Parts.literal]
  rw [oldPositive] at h1
  rw [oldDenominator] at h2
  simp only [Nat.zero_bits,List.length_nil,show (1:ℕ).bits.length=1 from rfl] at h1 h2
  omega

#print axioms correction_initialize_executes
end Maxwell.Continuum.Profile.Runtime
