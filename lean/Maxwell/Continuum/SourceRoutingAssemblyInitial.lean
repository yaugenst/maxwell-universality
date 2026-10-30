import Maxwell.Continuum.SourceRoutingAssemblyTraversalState

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem Frontier.initialized (heap rows total : ℕ) (root : Targets.Target rows total) (memory : ℕ→Bool)
    (hz : ∀p,heap ≤ p→p<heap+(2^(total+1)-1)*stride (2^(total+rows)) (total+rows+1)→memory p=false) :
    Frontier heap rows total root 0 memory := by
  intro d hd i
  have he : d=total := by omega
  subst d
  simp only [LabelsAt,Nat.zero_add]
  exact Leaves.initialized heap (2^(total+rows)) (total+rows+1) total rows
    (Nat.pow_le_pow_right (by decide) (by omega)) (by omega) memory hz i _

theorem Frontier.preserve (heap rows total : ℕ) (root : Targets.Target rows total)
    (before after : ℕ→Bool)
    (hf : Memory.Frame heap ((2^total-1)*stride (2^(total+rows)) (total+rows+1)) before after)
    (hs : Frontier heap rows total root 0 before) : Frontier heap rows total root 0 after := by
  intro d hd i
  have he : d=total := by omega
  subst d
  have frame : Memory.Frame (block heap (2^(total+rows)) (total+rows+1) 0)
      ((2^total-1)*stride (2^(total+rows)) (total+rows+1)) before after := by
    simpa only [block,Nat.zero_mul,Nat.add_zero] using hf
  have stored:=hs total (by omega) i
  simp only [LabelsAt,Nat.zero_add] at stored ⊢
  exact Leaves.preserve heap (2^(total+rows)) (total+rows+1) total rows 0 (2^total-1)
    (Nat.pow_le_pow_right (by decide) (by omega)) (by omega) (by omega)
    before after frame i _ stored

#print axioms Frontier.initialized
#print axioms Frontier.preserve
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
