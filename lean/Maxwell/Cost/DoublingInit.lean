import Maxwell.Cost.DoublingInit.Pass

namespace Maxwell.Cost.DoublingInit
open Structured
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing

/-- Initialize all four routing arrays from two encoded permutations. No
assumption is made on the previous contents of any output buffer. -/
theorem initializes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (a b : Equiv.Perm (Fin n)) (clock : List Bool)
    (hw : 0<layout.route.width) (hn : n≤2^layout.route.width)
    (hfit : n.bits.length≤layout.route.width) (hc : clock.length=layout.route.width)
    (hsep : layout.Separated n) (s : Store) (hnword : BankArray.Word s.val 96 n.bits)
    (h94 : Blank s.val 94) (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (ra : BitArray.Represents s.val.memory layout.inputA layout.route.width (DoublingPass.words layout.route.width (permutation a)))
    (rb : BitArray.Represents s.val.memory layout.inputB layout.route.width (DoublingPass.words layout.route.width (permutation b))) :
    ∃ cost t, cost≤passCost layout n ∧ Executes input tape passCode cost s t ∧
      Config layout [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      DoublingPass.Represents layout.route t.val.memory (Doubling.initial (Equiv.refl (Fin n)) (a*b)) (initialOutput n) ∧
      BitArray.Represents t.val.memory layout.inputA layout.route.width (DoublingPass.words layout.route.width (permutation a)) ∧
      BitArray.Represents t.val.memory layout.inputB layout.route.width (DoublingPass.words layout.route.width (permutation b)) ∧
      LoopFrame s.val t.val ∧
      DoublingPass.MemoryFrame layout.route n s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,cfgT,workT,t94,rep,frame,memoryFrame⟩ := pass_executes input tape layout a b clock
    hw hn hfit hc hsep s hnword h94 cfg work
    ⟨ra,rb,Prefix.zero _ _ _ _,Prefix.zero _ _ _ _,Prefix.zero _ _ _ _,Prefix.zero _ _ _ _⟩
  exact ⟨cost,t,hcost,he,cfgT,workT,t94,rep.complete,rep.inputA,rep.inputB,frame,memoryFrame⟩

theorem run {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (a b : Equiv.Perm (Fin n)) (clock : List Bool)
    (hw : 0<layout.route.width) (hn : n≤2^layout.route.width)
    (hfit : n.bits.length≤layout.route.width) (hc : clock.length=layout.route.width)
    (hsep : layout.Separated n) (s : Store) (hnword : BankArray.Word s.val 96 n.bits)
    (h94 : Blank s.val 94) (cfg : Config layout [] clock s.val) (work : Workspace s.val)
    (ra : BitArray.Represents s.val.memory layout.inputA layout.route.width (DoublingPass.words layout.route.width (permutation a)))
    (rb : BitArray.Represents s.val.memory layout.inputB layout.route.width (DoublingPass.words layout.route.width (permutation b))) :
    ∃ t : Store,
      (runPriced (passCode.compile.next input tape) (passCost layout n+1) s.val).finished = some (t.place passCode.size) ∧
      (runPriced (passCode.compile.next input tape) (passCost layout n+1) s.val).instructions≤passCost layout n ∧
      Config layout [] clock t.val ∧ Workspace t.val ∧ Blank t.val 94 ∧
      DoublingPass.Represents layout.route t.val.memory (Doubling.initial (Equiv.refl (Fin n)) (a*b)) (initialOutput n) ∧
      BitArray.Represents t.val.memory layout.inputA layout.route.width (DoublingPass.words layout.route.width (permutation a)) ∧
      BitArray.Represents t.val.memory layout.inputB layout.route.width (DoublingPass.words layout.route.width (permutation b)) ∧
      LoopFrame s.val t.val ∧
      DoublingPass.MemoryFrame layout.route n s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,ht⟩ := initializes input tape layout a b clock hw hn hfit hc hsep s hnword h94 cfg work ra rb
  have hr := he.compiled_run (passCost layout n+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

theorem passCost_bound (layout : Layout) (n : ℕ) :
    passCost layout n≤400000*(n+1)*(budget layout n.bits+1)^2 := by
  let b := budget layout n.bits
  have hl : n.bits.length≤b := by dsimp [b,budget,DoublingPass.budget]; omega
  have hb : b+1≤(b+1)^2 := by nlinarith
  have hc : (n+1)*(13*n.bits.length+15)≤(n+1)*(28*(b+1)^2) := by
    apply Nat.mul_le_mul_left
    nlinarith
  dsimp [passCost,loopCost]
  change _≤400000*(n+1)*(b+1)^2
  nlinarith

end Maxwell.Cost.DoublingInit
