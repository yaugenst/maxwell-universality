import Maxwell.Continuum.ChebyshevWaveRuntimeParameters

/-! Actual fixed setup of every nested-wave phase metadata word. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def parameterWorkspace : Finset ℕ := {0,1,2,3}∪parameterIds

theorem parameter_executes (Q P W : ℕ) (hQ : Q.bits.length≤W) (hP : P.bits.length≤W) (hW : 3≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank parameterIds (initialParameters Q P) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape parameterCode cost s t ∧ cost≤2^50*(W+2)^2 ∧
      Parameters Q P t ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame parameterWorkspace s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := NatAssign.stored_length parameterIds 670 678
    (by decide) (by decide) (by decide) (by decide) (initialParameters Q P) (by simp [initialParameters])
    input tape s hs hz
  change NatAssign.Bank parameterIds (scannedParameters Q P) s0.val at b0
  change c0≤48*(Q.bits.length+1)^2+1 at h0
  have hw : ∀i∈parameterIds,(scannedParameters Q P i).bits.length≤W := by
    intro i _
    by_cases h678 : i=678
    · subst i
      exact (Machin.Runtime.nat_bits_le_self _).trans hQ
    · simp only [scannedParameters,Function.update_of_ne h678,initialParameters]
      split_ifs <;> simp_all
  have hg (i : ℕ) (hi : i∈parameterIds) : 4 ≤ i := (parameterIds_range i hi).1.trans' (by decide)
  obtain ⟨c1,t,e1,h1,b1,z1,f1⟩ := NatAssign.executes parameterIds hg parameterInstructions
    parameterInstructions_valid (scannedParameters Q P) input tape s0 b0 z0
  have hprice := NatAssign.price_bound parameterIds parameterInstructions parameterInstructions_valid
    (scannedParameters Q P) W hw (by
      intro a ha
      simp only [parameterInstructions,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [NatAssign.Instruction.literalWidth,
          show (1:ℕ).bits.length=1 by decide,show (2:ℕ).bits.length=2 by decide,
          show (4:ℕ).bits.length=3 by decide] <;> omega)
  have hprice' : c1≤3000*8^11*(W+2)^2 := h1.trans hprice
  have hpow : (Q.bits.length+1)^2≤(W+2)^2 := Nat.pow_le_pow_left (by omega) 2
  have hone : 1≤(W+2)^2 := one_le_pow₀ (by omega)
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,(f0.mono ?_).trans (f1.mono ?_)⟩
  · have hc0 := h0.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 48 hpow) 1)
    omega
  · intro i hi
    have he : i=678 := Finset.mem_singleton.mp hi
    subst i
    exact Finset.mem_union_right _ (by decide)
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|hm
    · exact Finset.mem_union_left _ hz'
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
      apply Finset.mem_union_right
      have hv := parameterInstructions_valid a ha
      cases a <;> first | exact hv | exact hv.2.1

#print axioms parameter_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
