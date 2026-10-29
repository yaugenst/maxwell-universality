import Maxwell.Cost.CycleSplit.Finish
import Maxwell.Cost.CycleSplit.Representation
import Maxwell.Cost.DoublingPass.Complexity

namespace Maxwell.Cost.CycleSplit
open Structured DoublingPass
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing

def Frame (s t : BitRAMState) : Prop :=
  t.inputHead=s.inputHead ∧ t.randomCursor=s.randomCursor ∧ t.output=s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → ¬RoundPrivate i → i≠37 → i≠97 → t.tapes i=s.tapes i) ∧
  (∀ i, 15 ≤ i → i < 24 ∨ 31 < i → t.registers i=s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨hi,hr,ho,ht,hg⟩
  rcases k with ⟨ki,kr,ko,kt,kg⟩
  exact ⟨ki.trans hi,kr.trans hr,ko.trans ho,
    fun i hi hp h37 h97 => (kt i hi hp h37 h97).trans (ht i hi hp h37 h97),
    fun i hi hr => (kg i hi hr).trans (hg i hi hr)⟩

theorem Frame.of_init {s t : BitRAMState} (h : DoublingInit.LoopFrame s t) : Frame s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_,?_⟩
  · intro i hi hp h37 _
    apply h.2.2.2.1 i hi
    · intro he; exact hp (by simp [RoundPrivate,he])
    · intro he
      rcases he with he | he
      · exact h37 he
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))
    · intro he; exact hp (by simp [RoundPrivate,he])
  · intro i hi hr
    exact h.2.2.2.2 i hi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem Frame.of_computed {s t : BitRAMState} (h : CompleteFrame s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi hp _ h97 => h.2.2.2.1 i hi hp h97,h.2.2.2.2⟩

theorem Frame.of_adapter {s t : BitRAMState} (h : RoundFrame s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi hp _ _ => h.2.2.2.1 i hi hp,
   fun i hi hr => h.2.2.2.2 i hi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem Frame.of_finish {s t : BitRAMState} (h : DoublingPass.LoopFrame s t) : Frame s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_,?_⟩
  · intro i hi hp _ _
    apply h.2.2.2.1 i hi
    · intro he; exact hp (by simp [RoundPrivate,he])
    · intro he; exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))
    · intro he; exact hp (by simp [RoundPrivate,he])
  · intro i hi hr
    exact h.2.2.2.2 i hi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- One fixed finite program initializes, doubles, adapts its metadata, and
emits every alternating-cycle split bit to indexed bit memory. -/
def code : Code := .seq DoublingInit.passCode
  (.seq computedCode (.seq adapterCode finishCode))

def costCap (layout : DoublingInit.Layout) (n : ℕ) : ℕ :=
  let finalLayout := layoutAfter layout.route n.bits.length
  DoublingInit.passCost layout n + (computedCost layout.route n +
    (adapterCost finalLayout layout.inputA + finishCost (colorLayout finalLayout layout.inputA) n))

theorem executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : DoublingInit.Layout) (a b : Equiv.Perm (Fin n)) (clock : List Bool)
    (hw : 0<layout.route.width) (hn : n≤2^layout.route.width)
    (hfit : n.bits.length≤layout.route.width) (hc : clock.length=layout.route.width)
    (hsep : layout.Separated n) (s : Store) (hnword : BankArray.Word s.val 96 n.bits)
    (h94 : Blank s.val 94) (h95 : Blank s.val 95) (h97 : Blank s.val 97)
    (cfg : DoublingInit.Config layout [] clock s.val) (work : DoublingInit.Workspace s.val)
    (ra : BitArray.Represents s.val.memory layout.inputA layout.route.width (words layout.route.width (DoublingInit.permutation a)))
    (rb : BitArray.Represents s.val.memory layout.inputB layout.route.width (words layout.route.width (DoublingInit.permutation b))) :
    ∃ cost t, cost≤costCap layout n ∧ Executes input tape code cost s t ∧
      Config (colorLayout (layoutAfter layout.route n.bits.length) layout.inputA) [] clock t.val ∧
      DoublingInit.Workspace t.val ∧ Blank t.val 94 ∧ Blank t.val 95 ∧ Blank t.val 97 ∧
      BankArray.Word t.val 96 n.bits ∧
      BitArray.Represents t.val.memory (layoutAfter layout.route n.bits.length).newJump 1
        (ColorPass.colorWords (Doubling.indexedColors (Equiv.refl (Fin n)) a b)) ∧
      Frame s.val t.val ∧ MemoryFrame layout.route n s.val.memory t.val.memory := by
  obtain ⟨ic,i,hic,ei,cfgI,workI,i94,repI,ia,_,ifrm,imem⟩ := DoublingInit.initializes input tape layout a b clock
    hw hn hfit hc hsep s hnword h94 cfg work ra rb
  have keepI (k : ℕ) (h81 : k≠81) (hp : ¬DoublingInit.Private k) (h94 : k≠94) (hk : k=4 ∨ 10≤k) :=
    ifrm.2.2.2.1 k hk h81 hp h94
  obtain ⟨dc,d,out,hdc,ed,cfgD,workD,d94,d95,d97,d96,repD,dfrm,dmem⟩ := computed_executes input tape
    layout.route (Doubling.initial (Equiv.refl (Fin n)) (a*b)) (DoublingInit.initialOutput n) clock
    hw hn hc hsep.pingPong i
    (BankArray.word_of_eq (keepI 96 (by omega) (by simp [DoublingInit.Private,Private]) (by omega) (by omega)) hnword)
    i94 (RationalAccumulator.blank_of_eq (keepI 95 (by omega) (by simp [DoublingInit.Private,Private]) (by omega) (by omega)) h95)
    (RationalAccumulator.blank_of_eq (keepI 97 (by omega) (by simp [DoublingInit.Private,Private]) (by omega) (by omega)) h97)
    cfgI.route workI.1 repI
  let current := layoutAfter layout.route n.bits.length
  have pairingD : BankArray.Word d.val 98 layout.inputA.bits := BankArray.word_of_eq
    (dfrm.2.2.2.1 98 (by omega) (by simp [RoundPrivate,Private]) (by omega)) cfgI.inputA
  have raD : BitArray.Represents d.val.memory layout.inputA current.width (words current.width (DoublingInit.permutation a)) := by
    simpa [current] using (inputA_apart hsep).represents dmem ia
  have crD := color_represents current layout.inputA a b n.bits.length d.val.memory out raD repD
  obtain ⟨u,eu,cfgU,workU,um,ukeep,ufrm⟩ := adapter_executes input tape current layout.inputA clock d cfgD pairingD workD
  obtain ⟨fc,t,hfc,ef,cfgT,workT,t94,repT,tfrm,tmem⟩ := finish_executes input tape
    (colorLayout current layout.inputA) (ColorPass.comparisonState a b n.bits.length)
    (snapshotColors d.val.memory current.newJump n) clock
    (by simpa [colorLayout,current] using hw) (by simpa [colorLayout,current] using hn)
    (by simpa [colorLayout,current] using hc) rfl
    (color_separated (by simpa [current] using hw) (hsep.pingPong.after n.bits.length) ((inputA_apart hsep).after n.bits.length))
    u (BankArray.word_of_eq (ukeep 96 (by omega) (by omega)) d96)
    (RationalAccumulator.blank_of_eq (ukeep 94 (by omega) (by omega)) d94)
    cfgU workU (by simpa only [um] using crD)
  have keepT (k : ℕ) (hk : k=4 ∨ 10≤k) (h81 : k≠81) (hp : ¬Private k) (h94 : k≠94) := tfrm.2.2.2.1 k hk h81 hp h94
  have final37 : Blank t.val 37 := RationalAccumulator.blank_of_eq
    ((keepT 37 (by omega) (by omega) (by simp [Private]) (by omega)).trans
      ((ukeep 37 (by omega) (by omega)).trans (dfrm.2.2.2.1 37 (by omega) (by simp [RoundPrivate,Private]) (by omega)))) workI.2
  have t95 := RationalAccumulator.blank_of_eq
    ((keepT 95 (by omega) (by omega) (by simp [Private]) (by omega)).trans (ukeep 95 (by omega) (by omega))) d95
  have t97 := RationalAccumulator.blank_of_eq
    ((keepT 97 (by omega) (by omega) (by simp [Private]) (by omega)).trans (ukeep 97 (by omega) (by omega))) d97
  have t96 := BankArray.word_of_eq
    ((keepT 96 (by omega) (by omega) (by simp [Private]) (by omega)).trans (ukeep 96 (by omega) (by omega))) d96
  have mfFinal : MemoryFrame layout.route n u.val.memory t.val.memory := by
    have h := color_memory_frame (by simpa [current] using hw) tmem
    simpa only [current,memoryFrame_layoutAfter] using h
  refine ⟨ic+(dc+(adapterCost current layout.inputA+fc)),t,by dsimp [costCap,current] at hfc ⊢; omega,
    ei.seq (ed.seq (eu.seq ef)),cfgT,⟨workT,final37⟩,t94,t95,t97,t96,?_,
    (Frame.of_init ifrm).trans ((Frame.of_computed dfrm).trans ((Frame.of_adapter ufrm).trans (Frame.of_finish tfrm))),
    imem.trans (dmem.trans ((MemoryFrame.of_eq um).trans mfFinal))⟩
  simpa only [ColorPass.colors_bits,colorLayout,current] using repT.output

/-- The whole split runs under a cap computed from the actual encoded metadata. -/
theorem run {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : DoublingInit.Layout) (a b : Equiv.Perm (Fin n)) (clock : List Bool)
    (hw : 0 < layout.route.width) (hn : n ≤ 2^layout.route.width)
    (hfit : n.bits.length ≤ layout.route.width) (hc : clock.length = layout.route.width)
    (hsep : layout.Separated n) (s : Store) (hnword : BankArray.Word s.val 96 n.bits)
    (h94 : Blank s.val 94) (h95 : Blank s.val 95) (h97 : Blank s.val 97)
    (cfg : DoublingInit.Config layout [] clock s.val) (work : DoublingInit.Workspace s.val)
    (ra : BitArray.Represents s.val.memory layout.inputA layout.route.width (words layout.route.width (DoublingInit.permutation a)))
    (rb : BitArray.Represents s.val.memory layout.inputB layout.route.width (words layout.route.width (DoublingInit.permutation b))) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (costCap layout n+1) s.val).finished = some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costCap layout n+1) s.val).instructions ≤ costCap layout n ∧
      Config (colorLayout (layoutAfter layout.route n.bits.length) layout.inputA) [] clock t.val ∧
      DoublingInit.Workspace t.val ∧ Blank t.val 94 ∧ Blank t.val 95 ∧ Blank t.val 97 ∧
      BankArray.Word t.val 96 n.bits ∧
      BitArray.Represents t.val.memory (layoutAfter layout.route n.bits.length).newJump 1
        (ColorPass.colorWords (Doubling.indexedColors (Equiv.refl (Fin n)) a b)) ∧
      Frame s.val t.val ∧ MemoryFrame layout.route n s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,ht⟩ := executes input tape layout a b clock hw hn hfit hc hsep s hnword h94 h95 h97 cfg work ra rb
  have hr := he.compiled_run (costCap layout n+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.CycleSplit
