import Maxwell.Continuum.PhaseRuntimeSetupData

/-! Actual fixed-code execution of phase precision and order setup. -/
namespace Maxwell.Continuum.PhaseMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def setupCost (W : ℕ) : ℕ := 2^81*(W+2)^2

theorem initialValues_width (a b Q N W i : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) : (initialValues a b Q N i).bits.length≤W := by
  unfold initialValues
  split_ifs <;> first | assumption | simp

theorem scannedValues_width (a b Q N W i : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) : (scannedValues a b Q N i).bits.length≤W := by
  by_cases hi : i=654
  · subst i
    simpa only [scannedValues,Function.update_self] using
      (Machin.Runtime.nat_bits_le_self Q.bits.length).trans hQ
  · simpa only [scannedValues,Function.update_of_ne hi] using initialValues_width a b Q N W i ha hb hQ hN

theorem setup_literals (W : ℕ) (hW : 10≤W) : ∀a∈setup,a.literalWidth≤W := by
  simp [setup,NatAssign.Instruction.literalWidth,show (4:ℕ).bits.length=3 from rfl,
    show (800:ℕ).bits.length=10 from rfl,show (2:ℕ).bits.length=2 from rfl,
    show (13:ℕ).bits.length=4 from rfl]
  omega

theorem setupValues_width (a b Q N W i : ℕ) (hi : i∈ids)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (hW : 10≤W) : (setupValues a b Q N i).bits.length≤2^19*(W+1) := by
  have h := NatAssign.values_width_bound ids setup setup_valid (scannedValues a b Q N) W
    (fun j _ => scannedValues_width a b Q N W j ha hb hQ hN) (setup_literals W hW) i hi
  exact (Nat.le_succ _).trans h

theorem setup_executes (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b Q N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape setupCode cost s t ∧ cost≤setupCost W ∧
      NatAssign.Bank ids (setupValues a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,u,e0,h0,bu,zu,f0⟩ := NatAssign.stored_length ids 652 654 (by decide)
    (by decide) (by decide) (by decide) (initialValues a b Q N) (by simp [initialValues])
    input tape s hs hz
  change NatAssign.Bank ids (scannedValues a b Q N) u.val at bu
  change c0≤48*(Q.bits.length+1)^2+1 at h0
  obtain ⟨c1,t,e1,h1,bt,zt,f1⟩ := NatAssign.executes ids ids_ge setup setup_valid
    (scannedValues a b Q N) input tape u bu zu
  have hp := NatAssign.price_bound ids setup setup_valid (scannedValues a b Q N) W
    (fun i _ => scannedValues_width a b Q N W i ha hb hQ hN) (setup_literals W hW)
  have hc1 : c1≤2^80*(W+2)^2 := h1.trans (hp.trans (by
    change 3000*8^19*(W+2)^2≤2^80*(W+2)^2
    exact Nat.mul_le_mul_right _ (by norm_num)))
  have hc0 : c0≤49*(W+2)^2 := by
    have hx : 1≤(W+2)^2 := one_le_pow₀ (by omega)
    have hh := Nat.pow_le_pow_left (by omega : Q.bits.length+1≤W+2) 2
    omega
  refine ⟨c0+c1,t,e0.seq e1,?_,bt,zt,(f0.mono (by decide)).trans (f1.mono (by decide))⟩
  unfold setupCost
  calc
    _≤49*(W+2)^2+2^80*(W+2)^2 := Nat.add_le_add hc0 hc1
    _=(49+2^80)*(W+2)^2 := by ring
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

#print axioms setup_executes
end Maxwell.Continuum.PhaseMachine.Runtime
