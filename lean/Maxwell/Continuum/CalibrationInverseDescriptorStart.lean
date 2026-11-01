import Maxwell.Continuum.CalibrationInverseDescriptorMachine
import Maxwell.Cost.PhysicalMaterial.FixedSubtract

/-! Recover the Neumann countdown from the stored alias radius: R=K+2
gives the actual generated-inverse input K-1=R-3. -/
namespace Maxwell.Continuum.Calibration.InverseDescriptor
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] sources budget measured values rawWidth dimension slotWidth bankWidth

def startPlan : List NatAssign.Instruction := [.copy 311 304]
def initial (v : ℕ→ℕ) : ℕ→ℕ := Function.update v 304 (v 311-3)
def startCode : Code := .seq (NatAssign.code startPlan)
  (.seq (PhysicalMaterial.FixedSubtract.code 304 3) code)
def startChanged : Finset ℕ := insert 304 changed
def startCost (v : ℕ→ℕ) (B : ℕ) : ℕ :=
  3000*8*(B+2)^2+PhysicalMaterial.FixedSubtract.costBound 3 B+costBound (initial v) B

theorem initial_width (v : ℕ→ℕ) (B : ℕ) (hw:∀k∈ids,(v k).bits.length≤B) :
    ∀k∈ids,(initial v k).bits.length≤B := by
  intro k hk
  by_cases he:k=304
  · subst k
    simp only [initial,Function.update_self]
    have h:(v 311-3).bits.length≤(v 311).bits.length:=by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.sub_le (v 311) 3)
    exact h.trans (hw 311 (by decide))
  · simpa only [initial,Function.update_of_ne he] using hw k hk

theorem start_executes (v : ℕ→ℕ) (B : ℕ) (hB:11≤B) (hR:3≤v 311)
    (hw:∀k∈ids,(v k).bits.length≤B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb:NatAssign.Bank ids v s.val) (hz:NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape startCode cost s t ∧ cost≤startCost v B ∧
      NatAssign.Bank ids (values (initial v)) t.val ∧ NatAssign.Scratch t.val ∧
      (∀k∈ids,(values (initial v) k).bits.length≤bankWidth (initial v)) ∧
      BinaryPrecision.Frame startChanged s.val t.val := by
  have valid:∀a∈startPlan,a.Valid ids:=by simp [startPlan,NatAssign.Instruction.Valid,ids,sourceIds]
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩:=NatAssign.executes ids ids_ge startPlan valid v input tape s hb hz
  have price:=NatAssign.price_bound ids startPlan valid v B hw (by
    simp only [startPlan,List.mem_cons,List.not_mem_nil,or_false,forall_eq,NatAssign.Instruction.literalWidth]
    exact Nat.zero_le B)
  have stored:RationalAccumulator.Word u.val 304 (v 311):=by
    simpa only [startPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,Function.update_self] using b0 304 (by decide)
  obtain ⟨c1,u1,e1,hc1,w1,f1⟩:=PhysicalMaterial.FixedSubtract.executes 304 3 (v 311) hR input tape u stored
  have bank1:NatAssign.Bank ids (initial v) u1.val:=by
    intro k hk
    by_cases he:k=304
    · subst k
      simpa only [initial,Function.update_self] using w1
    · simpa only [initial,startPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
        NatAssign.Instruction.value,Function.update_of_ne he] using
        RationalAccumulator.word_of_eq (f1.tapes k (by simpa only [Finset.mem_singleton] using he)) (b0 k hk)
  have scratch1:NatAssign.Scratch u1.val:=fun k hk=>RationalAccumulator.blank_of_eq
    (f1.tapes k (by simp only [Finset.mem_singleton];omega)) (z0 k hk)
  obtain ⟨c2,t,e2,hc2,b2,z2,width,f2⟩:=executes (initial v) B hB (initial_width v B hw) input tape u1 bank1 scratch1
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,z2,width,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (Finset.subset_insert _ _)))⟩
  have p:c0≤3000*8*(B+2)^2:=by simpa only [startPlan,List.length_cons,List.length_nil,Nat.zero_add,pow_one] using hc0.trans price
  have h:=hw 311 (by decide)
  unfold PhysicalMaterial.FixedSubtract.costBound at hc1
  unfold startCost PhysicalMaterial.FixedSubtract.costBound
  omega

#print axioms start_executes
end Maxwell.Continuum.Calibration.InverseDescriptor
