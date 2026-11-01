import Maxwell.Continuum.ParameterBufferMachineStep
import Maxwell.Cost.SelectedParameters.LeastLoop

/-! The literal buffer search, from executed candidate arithmetic and rational
comparison to the first successful power of two. -/
namespace Maxwell.Continuum.Parameters.BufferMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] values width

def code : Code := .seq (NatAssign.code formulas) (LeastLoop.code 35 testCode stepCode)
def initialCost (N B : ℕ) : ℕ := arithmeticCost formulas (inputWidth N B)
def costBound (N B : ℕ) : ℕ := initialCost N B+testCost (width N B)+1+
  N*(stepCost N B+testCost (width N B)+1)

theorem initialize_executes (D : Data) (N B : ℕ) (hD : D.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (inputs D 0) s.val) (hs : ∀i,i<5→RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape (NatAssign.code formulas) cost s t ∧
      cost ≤ initialCost N B ∧ Ready D 0 (width N B) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hc,bt,st,hf⟩ := NatAssign.executes ids (fun i hi=>by have := ids_ge i hi;omega)
    formulas formulas_valid (inputs D 0) input tape s hb (fun i hi=>hs i (by omega))
  have hp := NatAssign.price_bound ids formulas formulas_valid (inputs D 0) (inputWidth N B)
    (fun i _=>inputs_width D 0 N B (Nat.zero_le _) hD i) (formulas_literals _)
  have hf' := hf.mono (show NatAssign.changes formulas⊆{0,1,2,3}∪ids by decide +kernel)
  refine ⟨cost,t,he,hc.trans hp,⟨values D 0,by simpa only [values] using bt,
    fifth_scratch hf' hs st,by intro i hi;rfl,values_width D 0 N B (Nat.zero_le _) hD,?_,?_⟩,nat_frame hf'⟩
  · simpa [inputs] using input_fields D 0 35 (by decide)
  · simpa [inputs] using input_fields D 0 36 (by decide)

theorem executes (D : Data) (e d B : ℕ) (hC : D.constant=2^e)
    (hm : 0<D.sourceSize) (hKd : 0<D.conditionDen) (hAn : 0<D.alphaNum) (hAd : 0<D.alphaDen)
    (hTn : 0<D.tauNum) (hTd : 0<D.tauDen) (hEn : 0<D.epsilonNum) (hEd : 0<D.epsilonDen)
    (hA : (D.alphaNum:ℚ)/D.alphaDen=alpha D.length d) (hD : D.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (inputs D 0) s.val) (hs : ∀i,i<5→RationalAccumulator.Blank s.val i) :
    let K := (D.conditionNum:ℚ)/D.conditionDen
    let ε := (D.epsilonNum:ℚ)/D.epsilonDen
    let τ := (D.tauNum:ℚ)/D.tauDen
    let hε : 0<ε := div_pos (by exact_mod_cast hEn) (by exact_mod_cast hEd)
    let hτ : 0<τ := div_pos (by exact_mod_cast hTn) (by exact_mod_cast hTd)
    let N := Nat.find (bufferSearch_exists e D.wells D.sourceSize D.length d D.span K ε τ hm hε hτ)
    ∃cost t,Executes input tape code cost s t ∧ cost ≤ costBound N B ∧ Ready D N (width N B) t ∧
      RationalAccumulator.Word t.val 2115
        (selectedBuffer e D.wells D.sourceSize D.length d D.span K ε τ hm hε hτ) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  let K : ℚ := (D.conditionNum:ℚ)/D.conditionDen
  let ε : ℚ := (D.epsilonNum:ℚ)/D.epsilonDen
  let τ : ℚ := (D.tauNum:ℚ)/D.tauDen
  have hε : 0<ε := div_pos (by exact_mod_cast hEn) (by exact_mod_cast hEd)
  have hτ : 0<τ := div_pos (by exact_mod_cast hTn) (by exact_mod_cast hTd)
  let hex := bufferSearch_exists e D.wells D.sourceSize D.length d D.span K ε τ hm hε hτ
  let N := Nat.find hex
  let P (n : ℕ) := BufferTest e D.wells D.sourceSize D.length d D.span K ε τ (2^n)
  let R (n : ℕ) (t : Store) := Ready D n (width N B) t ∧ BinaryPrecision.Frame workspace s.val t.val
  have htest : ∀n ≤ Nat.find hex,∀u,R n u→
      ∃cost t,Executes input tape testCode cost u t ∧ cost ≤ testCost (width N B) ∧
        R n t ∧ t.val.registers 35=decide (¬P n) := by
    intro n hn u hu
    obtain ⟨cost,t,he,hc,ht,hr,hf⟩ := test_executes D n (width N B) hKd hAn hTn hEn input tape u hu.1
    refine ⟨cost,t,he,hc,⟨ht,hu.2.trans hf⟩,hr.trans ?_⟩
    have hiff := predicate D e d n hC hm hKd hAn hAd hTn hTd hEn hEd hA
    change (tests.any (AllComparisons.failed (values D n))=false ↔ P n) at hiff
    cases hx : tests.any (AllComparisons.failed (values D n)) with
    | false => simp [hiff.mp hx]
    | true =>
      have hnp : ¬P n := by intro hp;have := hiff.mpr hp;rw [hx] at this;contradiction
      simp [hnp]
  have hnext : ∀n<Nat.find hex,∀u,R n u→
      ∃cost t,Executes input tape stepCode cost u t ∧ cost ≤ stepCost N B ∧ R (n+1) t := by
    intro n hn u hu
    obtain ⟨cost,t,he,hc,ht,hf⟩ := step_executes D n N B (by omega) hD input tape u hu.1
    exact ⟨cost,t,he,hc,ht,hu.2.trans hf⟩
  obtain ⟨ic,u,ei,hi,hu,hfu⟩ := initialize_executes D N B hD input tape s hb hs
  obtain ⟨lc,t,el,hl,ht⟩ := LeastLoop.executes P hex 35 testCode stepCode
    (testCost (width N B)) (stepCost N B) input tape R htest hnext u ⟨hu,hfu⟩
  refine ⟨ic+lc,t,ei.seq el,?_,ht.1,?_,ht.2⟩
  · change ic+lc ≤ costBound N B
    change lc ≤ testCost (width N B)+1+N*(stepCost N B+testCost (width N B)+1) at hl
    unfold costBound
    omega
  · obtain ⟨v,bt,_,hv,_⟩ := ht.1
    have h2115 := hv 2115 (by decide +kernel)
    have hval : v 2115=2^N := h2115.trans (by simpa [inputs] using input_fields D N 2115 (by decide))
    simpa only [hval,selectedBuffer,firstPower,firstPowerExponent] using bt 2115 (by decide +kernel)

#print axioms executes
end Maxwell.Continuum.Parameters.BufferMachine
