import Maxwell.Continuum.ParameterSpacingMachineStep
import Maxwell.Cost.SelectedParameters.LeastLoop

/-! One fixed finite program performs the first successful spacing search.
It computes every test operand, doubles the candidate, and squares both
exponential denominators. The stopping index is proved, never supplied. -/

namespace Maxwell.Continuum.Parameters.SpacingMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] values width

def code : Code := .seq (NatAssign.code formulas) (LeastLoop.code 35 testCode stepCode)
def initialCost (N B : ℕ) : ℕ := 3000*8^formulas.length*(inputWidth N B+2)^2
def costBound (N B : ℕ) : ℕ := initialCost N B+testCost (width N B)+1+
  N*(stepCost (width N B)+testCost (width N B)+1)

theorem initialize_executes (D : Data) (N B : ℕ) (hD : D.Width B)
    (input : List Bool) (randomTape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (inputs D 0) s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape (NatAssign.code formulas) cost s t ∧
      cost ≤ initialCost N B ∧ Ready D 0 (width N B) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hc,bt,st,hf⟩ := NatAssign.executes ids ids_ge formulas formulas_valid
    (inputs D 0) input randomTape s hb hs
  have hp := NatAssign.price_bound ids formulas formulas_valid (inputs D 0) (inputWidth N B)
    (fun i _ => inputs_width D 0 N B (Nat.zero_le _) hD i) (formulas_literals _)
  refine ⟨cost,t,he,hc.trans hp,⟨values D 0,by simpa only [values] using bt,st,by intro i hi;rfl,
    values_width D 0 N B (Nat.zero_le _) hD,?_,?_⟩,hf.mono (by decide +kernel)⟩
  · simpa [inputs] using input_fields D 0 35 (by decide)
  · simpa [inputs] using input_fields D 0 36 (by decide)

theorem executes (D : Data) (e B : ℕ) (hC : D.constant=2^e)
    (hKn : 0<D.conditionNum) (hKd : 0<D.conditionDen)
    (hEn : 0<D.epsilonNum) (hEd : 0<D.epsilonDen) (hD : D.Width B)
    (input : List Bool) (randomTape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (inputs D 0) s.val) (hs : NatAssign.Scratch s.val) :
    let K := (D.conditionNum:ℚ)/D.conditionDen
    let ε := (D.epsilonNum:ℚ)/D.epsilonDen
    let hK : 0<K := div_pos (by exact_mod_cast hKn) (by exact_mod_cast hKd)
    let hε : 0<ε := div_pos (by exact_mod_cast hEn) (by exact_mod_cast hEd)
    let N := Nat.find (spacingSearch_exists e D.length K ε hK hε)
    ∃ cost t, Executes input randomTape code cost s t ∧ cost≤costBound N B ∧
      Ready D N (width N B) t ∧
      RationalAccumulator.Word t.val 2006 (selectedSpacing e D.length K ε hK hε) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  let K : ℚ := (D.conditionNum:ℚ)/D.conditionDen
  let ε : ℚ := (D.epsilonNum:ℚ)/D.epsilonDen
  have hK : 0<K := div_pos (by exact_mod_cast hKn) (by exact_mod_cast hKd)
  have hε : 0<ε := div_pos (by exact_mod_cast hEn) (by exact_mod_cast hEd)
  let hex := spacingSearch_exists e D.length K ε hK hε
  let N := Nat.find hex
  let P (n : ℕ) := SpacingTest e D.length K ε (2^n)
  let R (n : ℕ) (t : Store) := Ready D n (width N B) t ∧
    BinaryPrecision.Frame workspace s.val t.val
  have htest : ∀ n≤Nat.find hex, ∀ u,R n u→
      ∃ cost t, Executes input randomTape testCode cost u t ∧ cost≤testCost (width N B) ∧
        R n t ∧ t.val.registers 35=decide (¬P n) := by
    intro n hn u hu
    obtain ⟨cost,t,he,hc,ht,hr,hf⟩ := test_executes D n (width N B) hKn hEd input randomTape u hu.1
    refine ⟨cost,t,he,hc,⟨ht,hu.2.trans hf⟩,hr.trans ?_⟩
    have hiff := predicate D e n hC hKn hKd hEd
    change (tests.any (AllComparisons.failed (values D n))=false ↔ P n) at hiff
    cases hx : tests.any (AllComparisons.failed (values D n)) with
    | false => simp [hiff.mp hx]
    | true =>
      have hnp : ¬P n := by intro hp;have := hiff.mpr hp;rw [hx] at this;contradiction
      simp [hnp]
  have hnext : ∀ n<Nat.find hex, ∀ u,R n u→
      ∃ cost t, Executes input randomTape stepCode cost u t ∧ cost≤stepCost (width N B) ∧ R (n+1) t := by
    intro n hn u hu
    obtain ⟨cost,t,he,hc,ht,hf⟩ := step_executes D n N B (by omega) hD input randomTape u hu.1
    exact ⟨cost,t,he,hc,ht,hu.2.trans hf⟩
  obtain ⟨ic,u,ei,hi,hu,hfu⟩ := initialize_executes D N B hD input randomTape s hb hs
  obtain ⟨lc,t,el,hl,ht⟩ := LeastLoop.executes P hex 35 testCode stepCode
    (testCost (width N B)) (stepCost (width N B)) input randomTape R htest hnext u ⟨hu,hfu⟩
  refine ⟨ic+lc,t,ei.seq el,?_,ht.1,?_,ht.2⟩
  · change ic+lc≤costBound N B
    change lc≤testCost (width N B)+1+N*(stepCost (width N B)+testCost (width N B)+1) at hl
    unfold costBound
    omega
  ·
    obtain ⟨v,bt,_,hv,_⟩ := ht.1
    have h2006 := hv 2006 (by decide)
    have hval : v 2006=2^N := h2006.trans (by simpa [inputs] using input_fields D N 2006 (by decide))
    simpa only [hval,selectedSpacing,firstPower,firstPowerExponent] using bt 2006 (by decide)

#print axioms executes

end Maxwell.Continuum.Parameters.SpacingMachine
