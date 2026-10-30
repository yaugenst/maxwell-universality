import Maxwell.Continuum.RationalArctanRuntimeCycle

/-! Fixed arctangent code, with a stored term count and an alternating sign
register. Every integer operation and loop test is charged. -/
namespace Maxwell.Continuum.RationalArctan.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def loop (countTape : ℕ) : Code := RationalDataflow.countedProgram countTape cycleStep
def loopCost (N W wordLength : ℕ) : ℕ :=
  (N+1)*(13*wordLength+15)+N*(2^64*(RationalArctan.width N W+2)^2+3)
def initialization : List NatAssign.Instruction :=
  RationalArctan.initialization++[.literal 619 1,.literal 628 2]
def initCode : Code := .seq (NatAssign.code initialization) (Code.atom (.literal 240 true))
def program (countTape : ℕ) : Code := .seq initCode (loop countTape)
def costBound (N W wordLength : ℕ) : ℕ := 2^48*(W+2)^2+2+loopCost N W wordLength
def loopWorkspace (countTape : ℕ) : Finset ℕ := insert countTape workspace

theorem count_frame (countTape : ℕ) {s t : Store} (hf : CountedShifted.Frame countTape s t) :
    BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val := by
  refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  intro i hi
  exact hf.2.2.2.2.2.1 i (by intro he;subst i;exact hi (Finset.mem_insert_self _ _))

theorem loop_executes (a b countTape N W : ℕ) (hcount : countTape∉ids) (hc4 : 4≤countTape)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hword : s.val.tapes countTape=BitTape.shifted word origin) (hn : addressValue word=N)
    (hs : CycleReady a b 0 s) :
    ∃cost t finalWord,Executes input tape (loop countTape) cost s t ∧
      cost≤loopCost N W word.length ∧ CycleReady a b N t ∧
      t.val.tapes countTape=BitTape.shifted finalWord origin ∧ finalWord.length=word.length ∧
      BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val := by
  let inv : ℕ→Store→Prop := fun remaining t => remaining≤N ∧
    CycleReady a b (N-remaining) t ∧ BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val
  have stable : ∀r u v,CountedShifted.Frame countTape u v → inv r u → inv r v := by
    intro r u v hf hh
    exact ⟨hh.1,hh.2.1.count_frame a b (N-r) countTape hcount hc4 hf,
      hh.2.2.trans (count_frame countTape hf)⟩
  have body : ∀r ys u,inv (r+1) u → u.val.tapes countTape=BitTape.shifted ys origin →
      addressValue ys=r → ∃cost v,Executes input tape cycleStep cost u v ∧ inv r v ∧
      v.val.tapes countTape=BitTape.shifted ys origin ∧ cost≤2^64*(RationalArctan.width N W+2)^2+3 := by
    intro r ys u hh hw _
    have hr := hh.1
    obtain ⟨cost,v,he,hc,hv,hf⟩ := cycleStep_executes a b (N-(r+1)) N W (by omega) ha hb input tape u hh.2.1
    have heq : N-(r+1)+1=N-r := by omega
    rw [heq] at hv
    have hout : countTape∉workspace := by
      intro hi
      simp only [workspace,RationalArctan.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      have hi' : countTape∈ids := by
        simp only [ids,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        omega
      exact hcount hi'
    exact ⟨cost,v,he,⟨by omega,hv,hh.2.2.trans (hf.mono (Finset.subset_insert _ _))⟩,
      (hf.tapes countTape hout).trans hw,hc⟩
  obtain ⟨cost,t,finalWord,he,ht,hw,hl,_,hcost⟩ := CountedShifted.executes countTape origin
    cycleStep input tape inv (fun _ => 2^64*(RationalArctan.width N W+2)^2+3) stable body
    N word s hn hword ⟨le_rfl,by simpa [inv] using hs,BinaryPrecision.Frame.refl _ _⟩
  refine ⟨cost,t,finalWord,he,?_,?_,hw,hl,ht.2.2⟩
  · simpa only [loopCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost
  · simpa only [Nat.sub_zero] using ht.2.1

theorem initialization_valid : ∀a∈initialization,a.Valid ids := by
  simp [initialization,RationalArctan.initialization,NatAssign.Instruction.Valid,ids,RationalArctan.ids]
theorem initialization_values (v : ℕ→ℕ) (i : ℕ) (hi : i∈ids) :
    NatAssign.values initialization v i=values (v 610) (v 611) 0 i := by
  simp only [ids,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl)
  all_goals simp [initialization,RationalArctan.initialization,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
    values,RationalArctan.values,RationalArctan.numerator,RationalArctan.denominator]

theorem initialize_executes (v : ℕ→ℕ) (W : ℕ) (hW : 2≤W) (hw : ∀i∈ids,(v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape initCode cost s t ∧ cost≤2^48*(W+2)^2+2 ∧
      CycleReady (v 610) (v 611) 0 t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,u,he,hc,hb,hu,hf⟩ := NatAssign.executes ids ids_ge initialization initialization_valid v input tape s hs hz
  have hW1 : 1≤W := by omega
  have hp := NatAssign.price_bound ids initialization initialization_valid v W hw
    (by simp [initialization,RationalArctan.initialization,NatAssign.Instruction.literalWidth,
      show (2:ℕ).bits.length=2 by decide,hW,hW1])
  have hc' : cost≤2^48*(W+2)^2 := by
    have hlen : initialization.length=9 := by rfl
    rw [hlen] at hp
    exact hc.trans (hp.trans (Nat.mul_le_mul_right _ (by norm_num)))
  let t := Store.ofState (u.val.setRegister 240 true)
  have advance : Executes input tape (Code.atom (.literal 240 true)) 2 u t := Executes.literal input tape u 240 true
  refine ⟨cost+2,t,he.seq advance,by omega,⟨⟨?_,hu⟩,rfl⟩,?_⟩
  · intro i hi
    have htbank : NatAssign.Bank ids (NatAssign.values initialization v) t.val := hb
    simpa only [initialization_values v i hi] using htbank i hi
  · have hsub : NatAssign.changes initialization⊆workspace := by
      simp [NatAssign.changes,initialization,RationalArctan.initialization,
        NatAssign.Instruction.target,workspace,RationalArctan.workspace]
      decide
    exact (hf.mono hsub).trans ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

theorem program_executes (countTape N W : ℕ) (v : ℕ→ℕ)
    (hcount : countTape∉ids) (hc4 : 4≤countTape) (hW : 2≤W) (hw : ∀i∈ids,(v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue word=N) (hword : s.val.tapes countTape=BitTape.shifted word origin)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t finalWord,Executes input tape (program countTape) cost s t ∧
      cost≤costBound N W word.length ∧ CycleReady (v 610) (v 611) N t ∧
      t.val.tapes countTape=BitTape.shifted finalWord origin ∧ finalWord.length=word.length ∧
      BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val := by
  obtain ⟨c0,u,e0,h0,hu,f0⟩ := initialize_executes v W hW hw input tape s hs hz
  have hsub : workspace⊆insert countTape workspace := Finset.subset_insert _ _
  have hout : countTape∉workspace := by
    intro hi
    simp only [workspace,RationalArctan.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    have hi' : countTape∈ids := by
      simp only [ids,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact hcount hi'
  obtain ⟨c1,t,finalWord,e1,h1,ht,htw,hl,f1⟩ := loop_executes (v 610) (v 611) countTape N W hcount hc4
    (hw 610 (by decide)) (hw 611 (by decide)) input tape word origin u ((f0.tapes countTape hout).trans hword) hn hu
  exact ⟨c0+c1,t,finalWord,e0.seq e1,by unfold costBound;omega,ht,htw,hl,(f0.mono hsub).trans f1⟩

#print axioms program_executes
end Maxwell.Continuum.RationalArctan.Runtime
