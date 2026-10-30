import Maxwell.Cost.RoutingPorts.Primitives
import Maxwell.Cost.RoutingPorts.Complete.Common
import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Fixed arithmetic for the routing-array sizes and disjoint addresses. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Startup
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def ids : Finset ℕ := {141,145,705,709,711,712,716,717,718,719}
def countStatements : List NatAssign.Instruction :=
  [.literal 712 4,.copy 705 709,.multiply 712 709,
    .copy 141 716,.multiply 712 716,.add 145 716]
def addressStatements : List NatAssign.Instruction :=
  [.copy 709 717,.multiply 711 717,.add 716 717,
    .copy 717 719,.copy 709 712,.multiply 711 712,.add 712 719,
    .copy 709 718,.literal 712 0]
def countValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values countStatements v
def addressValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values addressStatements v

theorem ids_lower (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem count_valid : ∀a∈countStatements, a.Valid ids := by
  simp [countStatements,NatAssign.Instruction.Valid,ids]
theorem address_valid : ∀a∈addressStatements, a.Valid ids := by
  simp [addressStatements,NatAssign.Instruction.Valid,ids]

theorem count_count (v : ℕ→ℕ) : countValues v 709=4*v 705 := by
  simp [countValues,countStatements,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
theorem count_base (v : ℕ→ℕ) : countValues v 716=v 145+4*v 141 := by
  simp [countValues,countStatements,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
theorem count_other (v : ℕ→ℕ) (i : ℕ) (h709 : i≠709) (h712 : i≠712) (h716 : i≠716) :
    countValues v i=v i := by
  simp [countValues,countStatements,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,h709,h712,h716]

theorem address_back (v : ℕ→ℕ) : addressValues v 717=v 716+v 709*v 711 := by
  simp [addressValues,addressStatements,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  ring
theorem address_end (v : ℕ→ℕ) : addressValues v 719=v 716+2*(v 709*v 711) := by
  simp [addressValues,addressStatements,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  ring
theorem address_clock (v : ℕ→ℕ) : addressValues v 718=v 709 := by
  simp [addressValues,addressStatements,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
theorem address_other (v : ℕ→ℕ) (i : ℕ)
    (h712 : i≠712) (h717 : i≠717) (h718 : i≠718) (h719 : i≠719) :
    addressValues v i=v i := by
  simp [addressValues,addressStatements,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,h712,h717,h718,h719]

def layout (n base : ℕ) (hn : 0<n) : Layout n where
  forward := base
  backward := base+n*n.bits.length
  clock := n.bits
  positive := hn
  clock_length := rfl
  separated := Or.inl le_rfl

theorem address_metadata (v : ℕ→ℕ) (hwidth : v 711=(v 709).bits.length)
    (hn : 0<v 709) (s : BitRAMState) (hs : NatAssign.Bank ids (addressValues v) s) :
    Metadata (layout (v 709) (v 716) hn) s ∧
      Word s 719 (v 716+2*(v 709*(v 709).bits.length)) ∧ Blank s 712 := by
  have hw (i : ℕ) (hi : i∈ids) := hs i hi
  have hc := hw 709 (by decide)
  have hb := hw 716 (by decide)
  have hsize := hw 711 (by decide)
  rw [address_other v 709 (by decide) (by decide) (by decide) (by decide)] at hc
  rw [address_other v 716 (by decide) (by decide) (by decide) (by decide)] at hb
  rw [address_other v 711 (by decide) (by decide) (by decide) (by decide),hwidth] at hsize
  have hback := hw 717 (by decide)
  rw [address_back,hwidth] at hback
  have hclock := hw 718 (by decide)
  rw [address_clock] at hclock
  have hend := hw 719 (by decide)
  rw [address_end,hwidth] at hend
  have hzero := hw 712 (by decide)
  have hz : addressValues v 712=0 := by
    simp [addressValues,addressStatements,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value]
  rw [hz] at hzero
  exact ⟨⟨hc,hsize,hb,hback,hclock⟩,hend,(RationalAccumulator.zero_word_iff_blank _ _).mp hzero⟩

theorem count_executes (v : ℕ→ℕ) (B : ℕ) (hB : 3≤B)
    (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃steps t, Executes input tape (NatAssign.code countStatements) steps s t ∧
      steps≤3000*8^6*(B+2)^2 ∧ NatAssign.Bank ids (countValues v) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (NatAssign.changes countStatements) s.val t.val := by
  obtain ⟨steps,t,he,hc,ht,hz',hf⟩ := NatAssign.executes ids ids_lower countStatements count_valid
    v input tape s hs hz
  have hb := NatAssign.price_bound ids countStatements count_valid v B hw (by
    simp only [countStatements,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [NatAssign.Instruction.literalWidth,show (4 : ℕ).bits.length=3 by decide]
    omega)
  exact ⟨steps,t,he,hc.trans hb,ht,hz',hf⟩

theorem address_executes (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hz : NatAssign.Scratch s.val) :
    ∃steps t, Executes input tape (NatAssign.code addressStatements) steps s t ∧
      steps≤3000*8^9*(B+2)^2 ∧ NatAssign.Bank ids (addressValues v) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (NatAssign.changes addressStatements) s.val t.val := by
  obtain ⟨steps,t,he,hc,ht,hz',hf⟩ := NatAssign.executes ids ids_lower addressStatements address_valid
    v input tape s hs hz
  have hb := NatAssign.price_bound ids addressStatements address_valid v B hw (by
    simp [addressStatements,NatAssign.Instruction.literalWidth])
  exact ⟨steps,t,he,hc.trans hb,ht,hz',hf⟩

#print axioms address_metadata
#print axioms count_executes
#print axioms address_executes

end Maxwell.Cost.RoutingPorts.Complete.Startup
