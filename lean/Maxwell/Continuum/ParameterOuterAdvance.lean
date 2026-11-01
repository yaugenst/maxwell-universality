import Maxwell.Continuum.ParameterOuterStageExecution

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def advance : List NatAssign.Instruction := [.add 2222 2206,.multiply 2223 2220,.multiply 2224 2221]
def advanceCost (W : ℕ) : ℕ := 3000*8^advance.length*(W+2)^2

theorem advance_valid : ∀a∈advance,a.Valid ids := by
  simp [advance,NatAssign.Instruction.Valid,ids,Compare.ids,extra]

theorem advance_values (D : Data) (k : ℕ) (v : ℕ→ℕ) (h : Core D k v) :
    Core D (k+1) (NatAssign.values advance v) := by
  have keep (i : ℕ) (hi : i≠2206 ∧ i≠2220 ∧ i≠2221) : NatAssign.values advance v i=v i := by
    apply NatAssign.values_preserves
    simpa [advance,NatAssign.Instruction.target] using hi
  constructor
  · have span : (fun j:Fin 3=>NatAssign.values advance v (2217+j.val))=(fun j:Fin 3=>v (2217+j.val)) := by
      funext j;apply keep;have := j.isLt;omega
    simpa only [dataOf,keep 2210 (by decide),keep 2211 (by decide),keep 2212 (by decide),
      keep 2213 (by decide),keep 2214 (by decide),keep 2215 (by decide),keep 2216 (by decide),span] using h.data
  · simp [advance,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,h.one,h.exponent,Nat.add_comm]
  · simp [advance,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,h.two,h.binary,pow_succ,Nat.mul_comm]
  · simp [advance,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,h.eight,h.length,stageLength,pow_succ,Nat.mul_comm]
  · exact (keep _ (by decide)).trans h.one
  · exact (keep _ (by decide)).trans h.two
  · exact (keep _ (by decide)).trans h.eight
  · exact (keep _ (by decide)).trans h.four
  · exact (keep _ (by decide)).trans h.slow

theorem advance_executes (D : Data) (k W : ℕ) (hu : 2^(k+1)+1 ≤ W) (hL : stageLength (k+1)+1 ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready D k W s) :
    ∃cost t,Executes input tape (NatAssign.code advance) cost s t ∧ cost ≤ advanceCost W ∧
      Ready D (k+1) W t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨v,hb,hsc,hw,hc⟩ := hs
  obtain ⟨cost,t,he,hp,bt,st,ft⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) advance advance_valid v input tape s hb hsc
  have ht := advance_values D k v hc
  have bits (n : ℕ) : n.bits.length ≤ n := by rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
  have ww : ∀i∈ids,(NatAssign.values advance v i).bits.length ≤ W := by
    intro i hi
    by_cases h6 : i=2206
    · subst i;rw [ht.exponent];have := bits (k+1);have := Nat.lt_two_pow_self (n:=k+1);omega
    by_cases h0 : i=2220
    · subst i;rw [ht.binary];exact (bits _).trans (by omega)
    by_cases h1 : i=2221
    · subst i;rw [ht.length];exact (bits _).trans (by omega)
    rw [NatAssign.values_preserves advance v i (by simp [advance,NatAssign.Instruction.target,h6,h0,h1])]
    exact hw i hi
  have hp' := NatAssign.price_bound ids advance advance_valid v W hw
    (by simp [advance,NatAssign.Instruction.literalWidth])
  exact ⟨cost,t,he,hp.trans hp',⟨_,bt,st,ww,ht⟩,ft.mono (by decide +kernel)⟩

#print axioms advance_executes
end Maxwell.Continuum.Parameters.OuterMachine
