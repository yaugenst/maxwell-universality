import Maxwell.Continuum.SourceRoutingNodeExecution

/-! The node descriptor is loaded from five runtime control words. Its
clock is an actual copy of the power-of-two count word. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.NodeSetup
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def controls : Finset ℕ := {800,801,802,803,804}
def ids : Finset ℕ := controls∪RoutingAllocator.ids
def initial (q : ℕ→ℕ) (i : ℕ) : ℕ := if i∈controls then q i else 0
def descriptor (q : ℕ→ℕ) (i : ℕ) : ℕ :=
  if i=190 then q 800 else if i=191 then q 801 else if i=192 then q 802 else
  if i=193 then q 803 else if i=194 then q 804 else 0
def statements : List NatAssign.Instruction :=
  [.copy 800 190,.copy 801 191,.copy 802 192,.copy 803 193,.copy 804 194]
def code : Code := .seq (NatAssign.code statements) (.call (WordTransfer.clone 191 83))
def work : Finset ℕ := NatAssign.changes statements∪{83}
def bound (B : ℕ) : ℕ := 3000*8^5*(B+2)^2+15*B+17

theorem valid : ∀a∈statements,a.Valid ids := by
  simp [statements,NatAssign.Instruction.Valid,ids,controls,RoutingAllocator.ids]

theorem node_values (q : ℕ→ℕ) (i : ℕ) (hi : i∈RoutingAllocator.ids) :
    NatAssign.values statements (initial q) i=descriptor q i := by
  simp only [RoutingAllocator.ids,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [statements,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,initial,controls,descriptor]

private theorem scratch (s : BitRAMState) (hs : DoublingInit.Workspace s) : NatAssign.Scratch s := by
  intro i hi
  interval_cases i
  · exact hs.1.1.1
  · exact hs.1.1.2.1
  · exact hs.1.1.2.2.1
  · exact hs.1.1.2.2.2.1

private theorem workspace {s t : BitRAMState} (hs : DoublingInit.Workspace s)
    (hz : NatAssign.Scratch t) (hf : BinaryPrecision.Frame (NatAssign.changes statements) s t) :
    DoublingInit.Workspace t := by
  have keep (i : ℕ) (hi : i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=37 ∨ (88 ≤ i ∧ i ≤ 92)) :
      t.tapes i=s.tapes i := by
    apply hf.tapes
    have he : NatAssign.changes statements=({0,1,2,3,190,191,192,193,194}:Finset ℕ) := by decide
    rw [he]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  refine ⟨⟨⟨hz 0 (by omega),hz 1 (by omega),hz 2 (by omega),hz 3 (by omega),
    ?_,?_,?_,?_⟩,?_,?_⟩,?_⟩
  · exact RationalAccumulator.blank_of_eq (keep 5 (by omega)) hs.1.1.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 6 (by omega)) hs.1.1.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 8 (by omega)) hs.1.1.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 9 (by omega)) hs.1.1.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (keep 7 (by omega)) hs.1.2.1
  · intro i hi
    exact RationalAccumulator.blank_of_eq (keep i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi)))))))
      (hs.1.2.2 i hi)
  · exact RationalAccumulator.blank_of_eq (keep 37 (by omega)) hs.2

theorem executes (q : ℕ→ℕ) (B : ℕ) (hq : ∀i∈controls,(q i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hbank : NatAssign.Bank ids (initial q) s.val) (hs : DoublingInit.Workspace s.val)
    (h83 : Blank s.val 83) (hextra : ∀i∈Node.extra,Blank s.val i) :
    ∃steps t, Executes input tape code steps s t ∧ steps ≤ bound B ∧
      Node.Ready (descriptor q) (q 801).bits t.val ∧ BinaryPrecision.Frame work s.val t.val := by
  have hv : ∀i∈ids,(initial q i).bits.length ≤ B := by
    intro i _
    by_cases hi : i∈controls
    · simpa [initial,hi] using hq i hi
    · simp [initial,hi]
  obtain ⟨ac,a,ea,hac,ab,az,af⟩ := NatAssign.executes ids
    (by intro i hi; simp only [ids,controls,RoutingAllocator.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hi; omega) statements valid (initial q)
    input tape s hbank (scratch _ hs)
  have cost := NatAssign.price_bound ids statements valid (initial q) B hv
    (by simp [statements,NatAssign.Instruction.literalWidth])
  have an : RationalAccumulator.Word a.val 191 (q 801) := by
    have hh := ab 191 (by decide)
    rw [node_values q 191 (by decide)] at hh
    simpa [descriptor] using hh
  have blank83 : Blank a.val 83 := RationalAccumulator.blank_of_eq (af.tapes 83 (by decide)) h83
  obtain ⟨no,hno⟩ := an
  obtain ⟨co,hco⟩ := blank83
  obtain ⟨t,ec,tt,tf⟩ := WordCall.clone 191 83 (by decide) input tape (q 801).bits no co a hno hco
  have cf : BinaryPrecision.Frame {83} a.val t.val := by
    refine ⟨tf.1,tf.2.1,tf.2.2.1,tf.2.2.2.1,tf.2.2.2.2.1,?_⟩
    intro i hi
    rw [tt,Function.update_of_ne (show i≠83 by simpa using hi)]
  have ready : Node.Ready (descriptor q) (q 801).bits t.val := by
    refine ⟨?_,?_,⟨co,by simp only [tt,Function.update_self]⟩,?_⟩
    · intro i hi
      have hh := ab i (Finset.mem_union_right _ hi)
      rw [node_values q i hi] at hh
      apply RationalAccumulator.word_of_eq (cf.tapes i ?_) hh
      simp only [Finset.mem_singleton]
      simp only [RoutingAllocator.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    · apply DoublingInit.workspace_of_tapes (s:=a.val) (w:=workspace hs az af)
      intro i hi
      apply cf.tapes
      simp only [Finset.mem_singleton]
      dsimp [DoublingInit.Private,DoublingPass.Private] at hi
      omega
    · intro i hi
      apply RationalAccumulator.blank_of_eq ((cf.tapes i ?_).trans (af.tapes i ?_)) (hextra i hi)
      all_goals simp only [Node.extra,Finset.mem_insert,Finset.mem_singleton] at hi
      · simp only [Finset.mem_singleton]; omega
      · rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  refine ⟨ac+(15*(q 801).bits.length+17),t,ea.seq ec,?_,ready,
    (af.mono (Finset.subset_union_left)).trans (cf.mono (Finset.subset_union_right))⟩
  have hh := hq 801 (by decide)
  change NatAssign.price statements (initial q) ≤ 3000*8^5*(B+2)^2 at cost
  dsimp only [bound]
  omega

theorem clock_length (q : ℕ→ℕ) (k : ℕ) (hn : q 801=2*2^k) : (q 801).bits.length=k+2 := by
  rw [hn,←pow_succ',Nat.size_eq_bits_len,Nat.size_pow]

#print axioms executes
#print axioms clock_length

end Maxwell.Cost.RoutingPorts.Complete.Tree.NodeSetup
