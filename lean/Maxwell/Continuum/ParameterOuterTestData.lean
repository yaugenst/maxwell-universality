import Maxwell.Continuum.ParameterOuterBufferStage
import Maxwell.Continuum.ParameterOuterDecayMachine
import Maxwell.Continuum.ParameterOuterSearch

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def stageRetained : Finset ℕ := retained∪{2227,2228,2229,2243,2234,2237,2244,2245,2246,2247}
structure StageOutputs (D : Data) (hD : D.Positive) (e k : ℕ) (v : ℕ→ℕ) : Prop where
  core : Core D k v
  spacing : SpacingOutputs D hD e k v
  tau : TauOutputs D hD e k v
  buffer : BufferOutputs D hD e k v

theorem StageOutputs.congr {D : Data} {hD : D.Positive} {e k : ℕ} {v w : ℕ→ℕ}
    (h : StageOutputs D hD e k v) (he : ∀i∈stageRetained,w i=v i) : StageOutputs D hD e k w := by
  refine ⟨h.core.congr (fun i hi=>he i (Finset.mem_union_left _ hi)),?_,?_,?_⟩
  · exact ⟨(he _ (by decide +kernel)).trans h.spacing.spacing,
      (he _ (by decide +kernel)).trans h.spacing.zetaDen,
      (he _ (by decide +kernel)).trans h.spacing.alphaNum,
      (he _ (by decide +kernel)).trans h.spacing.alphaDen⟩
  · exact ⟨(he _ (by decide +kernel)).trans h.tau.numerator,
      (he _ (by decide +kernel)).trans h.tau.denominator⟩
  · exact ⟨(he _ (by decide +kernel)).trans h.buffer.buffer,
      (he _ (by decide +kernel)).trans h.buffer.box,
      (he _ (by decide +kernel)).trans h.buffer.numerator,
      (he _ (by decide +kernel)).trans h.buffer.denominator⟩

theorem decayValues_other (v : ℕ→ℕ) (source quotient target i : ℕ)
    (hi : i∉decayClears quotient target) : decayValues v source quotient target i=v i := by
  have hq : i≠quotient := by intro h;apply hi;simp [decayClears,h]
  have ht : i≠target := by intro h;apply hi;simp [decayClears,h]
  simp only [decayValues,Function.update_of_ne hq,Function.update_of_ne ht,decayReset,
    NatAssign.values_literals,ite_eq_right hi]

def decayed (v : ℕ→ℕ) : ℕ→ℕ := decayValues (decayValues v 2220 2250 2251) 2221 2252 2253

theorem decayed_other (v : ℕ→ℕ) (i : ℕ) (hi : i∈stageRetained) : decayed v i=v i := by
  have hi1 : i∉decayClears 2250 2251 := by
    simp only [stageRetained,retained,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
    simp [decayClears];omega
  have hi2 : i∉decayClears 2252 2253 := by
    simp only [stageRetained,retained,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
    simp [decayClears];omega
  rw [decayed,decayValues_other _ _ _ _ _ hi2,decayValues_other _ _ _ _ _ hi1]

theorem decayed_fields (v : ℕ→ℕ) :
    decayed v 2251=2^(v 2220/slowDivisor) ∧ decayed v 2253=2^(v 2221/slowDivisor) := by
  constructor
  · rw [decayed,decayValues_other _ _ _ _ _ (by simp [decayClears])]
    simp [decayValues]
  · simp only [decayed,decayValues,Function.update_self]
    change 2^(decayValues v 2220 2250 2251 2221/slowDivisor)=2^(v 2221/slowDivisor)
    rw [show decayValues v 2220 2250 2251 2221=v 2221 from decayValues_other _ _ _ _ _ (by simp [decayClears])]

def tailPrepare : List NatAssign.Instruction := prepareTail++Rational.clear
def tailSources : Finset ℕ := {2210,2212,2221,2225,2228}
def tailInputWidth (B : ℕ) : ℕ := 2^tailPrepare.length*(B+1)

theorem tailPrepare_valid : ∀a∈tailPrepare,a.Valid ids := by
  simp only [tailPrepare,List.mem_append]
  intro a ha
  rcases ha with ha|ha
  · exact prepareTail_valid a ha
  · simp only [Rational.clear,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [NatAssign.Instruction.Valid,ids,Compare.ids]

theorem tailPrepare_fields (v : ℕ→ℕ) (h4 : v 2225=4) :
    NatAssign.values tailPrepare v 2260=OuterStopping.tailNumerator (v 2210) (v 2212) (v 2221) (v 2228) ∧
    NatAssign.values tailPrepare v 35=0 ∧ NatAssign.values tailPrepare v 36=0 := by
  rw [tailPrepare,NatAssign.values_append]
  simp only [Rational.clear,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update_self]
  exact ⟨prepareTail_value v h4,rfl,trivial⟩

theorem tests_enabled (D : Data) (hD : D.Positive) (e k : ℕ) (v : ℕ→ℕ)
    (hs : StageOutputs D hD e k v) : ∀q∈tests,AllComparisons.Enabled v q := by
  have hk := hD.conditionDen
  have he := hD.epsilonNum
  have hL := stageLength_pos k
  have hden : 0<v 2247 := by
    rw [hs.buffer.denominator]
    simp only [BufferMachine.denominator,Data.buffer]
    positivity
  simpa [tests,AllComparisons.Enabled,hs.core.one] using hden

theorem tests_iff (D : Data) (hD : D.Positive) (e k : ℕ) (hC : D.constant=2^e)
    (v : ℕ→ℕ) (hs : StageOutputs D hD e k v)
    (hl : v 2251=2^((2^k)/slowDivisor)) (ht : v 2253=2^(stageLength k/slowDivisor))
    (hn : v 2260=OuterStopping.tailNumerator D.constant D.wells (stageLength k)
      (3^(stageSpacing (D.input hD) e k))) :
    tests.any (AllComparisons.failed v)=false ↔ OuterTest (D.input hD) e k := by
  have hL := stageLength_pos k
  have leak := BufferMachine.comparison_iff (D.buffer hD e k) e (stageSpacing (D.input hD) e k)
    (stageBuffer (D.input hD) e k) (2^k) hC hD.sourceSize hD.conditionDen
    (by dsimp only [Data.buffer];positivity) (by dsimp only [Data.buffer];positivity)
    (by change 0<1;decide) (by dsimp only [Data.buffer,Data.detuningDen];positivity)
    hD.epsilonNum hD.epsilonDen (D.buffer_alpha hD e k)
  simp only [D.buffer_tau hD e k] at leak
  change (BufferMachine.numerator (D.buffer hD e k) (stageBuffer (D.input hD) e k):ℚ)/
    BufferMachine.denominator (D.buffer hD e k) ≤ (2:ℚ)^((2^k)/slowDivisor) ↔
      LeakageTest (D.input hD) e k at leak
  have tail := OuterStopping.tail_comparison D.constant D.wells (stageLength k)
    (3^(stageSpacing (D.input hD) e k)) e (stageSpacing (D.input hD) e k) hC rfl
  change (OuterStopping.tailNumerator D.constant D.wells (stageLength k)
    (3^(stageSpacing (D.input hD) e k)):ℚ) ≤ (2:ℚ)^(stageLength k/slowDivisor) ↔
      TailTest (D.input hD) e k at tail
  simpa only [tests,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_false_iff,
    AllComparisons.failed,decide_eq_false_iff_not,not_lt,hs.core.one,Nat.cast_one,div_one,
    hs.buffer.numerator,hs.buffer.denominator,hl,ht,hn,Nat.cast_pow,Nat.cast_ofNat,OuterTest] using
    and_congr leak tail

#print axioms tests_iff
end Maxwell.Continuum.Parameters.OuterMachine
