import Maxwell.Continuum.RationalTaylorRuntimeCycle

/-! A single finite Taylor program reads its term count from a stored word.
All growing loops are actual counted machine loops. -/
namespace Maxwell.Continuum.RationalTaylor.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def loop (cycle : Cycle) (countTape : ℕ) : Code := RationalDataflow.countedProgram countTape (cycleStep cycle)
def loopCost (N W wordLength : ℕ) : ℕ :=
  (N+1)*(13*wordLength+15)+N*(2^44*(width N W+2)^2+6)
def initialization (cycle : Cycle) : List NatAssign.Instruction :=
  RationalTaylor.initialization (cycle 0)++[.literal 607 1,.literal 608 1]
def initCode (cycle : Cycle) : Code :=
  .seq (NatAssign.code (initialization cycle))
    (.seq (Code.atom (.literal 240 true)) (Code.atom (.literal 241 false)))
def program (cycle : Cycle) (countTape : ℕ) : Code := .seq (initCode cycle) (loop cycle countTape)
def costBound (N W wordLength : ℕ) : ℕ := 2^44*(W+2)^2+4+loopCost N W wordLength
def loopWorkspace (countTape : ℕ) : Finset ℕ := insert countTape workspace

theorem CycleReady.count_frame_of (a b : ℕ) (cycle : Cycle) (n countTape : ℕ)
    (hc : countTape∉ids) (hc4 : 4≤countTape) {s t : Store}
    (hs : CycleReady a b cycle n s) (hf : CountedShifted.Frame countTape s t) :
    CycleReady a b cycle n t := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro i hi
    exact word_of_eq (hf.2.2.2.2.2.1 i (by intro he;subst i;exact hc hi)) (hs.data.bank i hi)
  · intro i hi
    exact blank_of_eq (hf.2.2.2.2.2.1 i (by omega)) (hs.data.scratch i hi)
  · exact (hf.2.2.2.2.2.2 240 (by decide) (by decide) (by decide) (by decide)).trans hs.low
  · exact (hf.2.2.2.2.2.2 241 (by decide) (by decide) (by decide) (by decide)).trans hs.high

theorem count_frame (countTape : ℕ) {s t : Store} (hf : CountedShifted.Frame countTape s t) :
    BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val := by
  refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  intro i hi
  exact hf.2.2.2.2.2.1 i (by intro he;subst i;exact hi (Finset.mem_insert_self _ _))

theorem loop_executes (a b : ℕ) (cycle : Cycle) (countTape N W : ℕ)
    (hcount : countTape∉ids) (hc4 : 4≤countTape)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hword : s.val.tapes countTape=BitTape.shifted word origin) (hn : addressValue word=N)
    (hs : CycleReady a b cycle 0 s) :
    ∃cost t finalWord,Executes input tape (loop cycle countTape) cost s t ∧
      cost≤loopCost N W word.length ∧ CycleReady a b cycle N t ∧
      t.val.tapes countTape=BitTape.shifted finalWord origin ∧ finalWord.length=word.length ∧
      BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val := by
  let inv : ℕ→Store→Prop := fun remaining t => remaining≤N ∧
    CycleReady a b cycle (N-remaining) t ∧ BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val
  have stable : ∀r u v,CountedShifted.Frame countTape u v → inv r u → inv r v := by
    intro r u v hf hh
    exact ⟨hh.1,hh.2.1.count_frame_of a b cycle (N-r) countTape hcount hc4 hf,
      hh.2.2.trans (count_frame countTape hf)⟩
  have body : ∀r ys u,inv (r+1) u → u.val.tapes countTape=BitTape.shifted ys origin →
      addressValue ys=r → ∃cost v,Executes input tape (cycleStep cycle) cost u v ∧ inv r v ∧
      v.val.tapes countTape=BitTape.shifted ys origin ∧ cost≤2^44*(width N W+2)^2+6 := by
    intro r ys u hh hw _
    have hr := hh.1
    obtain ⟨cost,v,he,hc,hv,hf⟩ := cycleStep_executes a b cycle (N-(r+1)) N W
      (by omega) ha hb input tape u hh.2.1
    have heq : N-(r+1)+1=N-r := by omega
    rw [heq] at hv
    have hout : countTape∉workspace := by
      intro hi
      simp only [workspace,RationalTaylor.workspace,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton] at hi
      have hi' : countTape∈ids := by
        simp only [ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        omega
      exact hcount hi'
    exact ⟨cost,v,he,⟨by omega,hv,hh.2.2.trans (hf.mono (Finset.subset_insert _ _))⟩,
      (hf.tapes countTape hout).trans hw,hc⟩
  obtain ⟨cost,t,finalWord,he,ht,hw,hl,_,hcost⟩ := CountedShifted.executes countTape origin
    (cycleStep cycle) input tape inv (fun _ => 2^44*(width N W+2)^2+6) stable body
    N word s hn hword ⟨le_rfl,by simpa [inv] using hs,BinaryPrecision.Frame.refl _ _⟩
  refine ⟨cost,t,finalWord,he,?_,?_,hw,hl,ht.2.2⟩
  · simpa only [loopCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost
  · simpa only [Nat.sub_zero] using ht.2.1

theorem initialization_valid (cycle : Cycle) : ∀a∈initialization cycle,a.Valid ids := by
  cases cycle 0 <;> simp [initialization,RationalTaylor.initialization,
    NatAssign.Instruction.Valid,ids,RationalTaylor.ids]

theorem initialization_values (cycle : Cycle) (v : ℕ→ℕ) (i : ℕ) (hi : i∈ids) :
    NatAssign.values (initialization cycle) v i=values (v 600) (v 601) (cycleSigns cycle) 0 i := by
  simp only [ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl)
  all_goals simp [initialization,RationalTaylor.initialization,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
    values,RationalTaylor.values,numerator,denominator,cycleSigns]

theorem initialize_executes (cycle : Cycle) (v : ℕ→ℕ) (W : ℕ) (hW : 1≤W)
    (hw : ∀i∈ids,(v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (initCode cycle) cost s t ∧ cost≤2^44*(W+2)^2+4 ∧
      CycleReady (v 600) (v 601) cycle 0 t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,u,he,hc,hb,hu,hf⟩ := NatAssign.executes ids ids_ge (initialization cycle)
    (initialization_valid cycle) v input tape s hs hz
  have hp := NatAssign.price_bound ids (initialization cycle) (initialization_valid cycle) v W hw
    (by cases hsign : cycle 0 <;> simp [initialization,RationalTaylor.initialization,
      NatAssign.Instruction.literalWidth,hsign,Sign.positive,Sign.negative,hW])
  have hc' : cost≤2^44*(W+2)^2 := by
    have hlen : (initialization cycle).length=7 := by simp [initialization,RationalTaylor.initialization]
    rw [hlen] at hp
    exact hc.trans (hp.trans (Nat.mul_le_mul_right _ (by norm_num)))
  let u1 := Store.ofState (u.val.setRegister 240 true)
  let t := Store.ofState (u1.val.setRegister 241 false)
  have e1 : Executes input tape (Code.atom (.literal 240 true)) 2 u u1 := Executes.literal input tape u 240 true
  have e2 : Executes input tape (Code.atom (.literal 241 false)) 2 u1 t := Executes.literal input tape u1 241 false
  refine ⟨cost+(2+2),t,he.seq (e1.seq e2),by omega,⟨⟨?_,hu⟩,rfl,rfl⟩,?_⟩
  · intro i hi
    have htbank : NatAssign.Bank ids (NatAssign.values (initialization cycle) v) t.val := hb
    simpa only [initialization_values cycle v i hi] using htbank i hi
  · have hsub : NatAssign.changes (initialization cycle)⊆workspace := by
      simp [NatAssign.changes,initialization,RationalTaylor.initialization,
        NatAssign.Instruction.target,workspace,RationalTaylor.workspace]
      decide
    exact (hf.mono hsub).trans ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

theorem program_executes (cycle : Cycle) (countTape N W : ℕ) (v : ℕ→ℕ)
    (hcount : countTape∉ids) (hc4 : 4≤countTape) (hW : 1≤W)
    (hw : ∀i∈ids,(v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (origin : ℤ) (s : Store)
    (hn : addressValue word=N) (hword : s.val.tapes countTape=BitTape.shifted word origin)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t finalWord,Executes input tape (program cycle countTape) cost s t ∧
      cost≤costBound N W word.length ∧ CycleReady (v 600) (v 601) cycle N t ∧
      t.val.tapes countTape=BitTape.shifted finalWord origin ∧ finalWord.length=word.length ∧
      BinaryPrecision.Frame (loopWorkspace countTape) s.val t.val := by
  obtain ⟨c0,u,e0,h0,hu,f0⟩ := initialize_executes cycle v W hW hw input tape s hs hz
  have hsub : workspace⊆insert countTape workspace := Finset.subset_insert _ _
  have hout : countTape∉workspace := by
    intro hi
    simp only [workspace,RationalTaylor.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    have hi' : countTape∈ids := by
      simp only [ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact hcount hi'
  obtain ⟨c1,t,finalWord,e1,h1,ht,htw,hl,f1⟩ := loop_executes (v 600) (v 601) cycle countTape N W
    hcount hc4 (hw 600 (by decide)) (hw 601 (by decide)) input tape word origin u
    ((f0.tapes countTape hout).trans hword) hn hu
  exact ⟨c0+c1,t,finalWord,e0.seq e1,by unfold costBound;omega,ht,htw,hl,(f0.mono hsub).trans f1⟩

#print axioms loop_executes
#print axioms program_executes
end Maxwell.Continuum.RationalTaylor.Runtime
