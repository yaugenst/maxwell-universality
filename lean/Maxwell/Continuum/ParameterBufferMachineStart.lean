import Maxwell.Continuum.ParameterBufferMachine

/-! Restart the buffer search from fifteen actual operand words. All
candidate, division, arithmetic, and comparison words are overwritten. -/
namespace Maxwell.Continuum.Parameters.BufferMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
attribute [local irreducible] values width

def dataOf (v : ℕ→ℕ) : Data :=
  ⟨v 2100,v 2101,v 2102,v 2103,v 2104,v 2105,v 2106,v 2107,v 2108,v 2109,v 2110,v 2111,
    fun j=>v (2112+j.val)⟩
def zeroData : Data := ⟨0,0,0,0,0,0,0,0,0,0,0,0,fun _=>0⟩
def restartTargets : List ℕ := [30,31,32,33,34,35,36,220,221,222,223]++(List.range 42).map (2115+·)
def restartInstructions : List NatAssign.Instruction :=
  restartTargets.map fun i=>.literal i (inputs zeroData 0 i)
def restartCode : Code := .seq (NatAssign.code restartInstructions) code
def resetCost (B : ℕ) : ℕ := arithmeticCost restartInstructions (B+1031)

theorem restart_valid : ∀a∈restartInstructions,a.Valid ids := by
  simp [restartInstructions,restartTargets,List.range_succ,NatAssign.Instruction.Valid,ids,Compare.ids,extra]

theorem restart_values (v : ℕ→ℕ) (i : ℕ) (hi : i∈ids) :
    NatAssign.values restartInstructions v i=inputs (dataOf v) 0 i := by
  rw [restartInstructions,NatAssign.values_literals]
  simp only [ids,Compare.ids,extra,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with (h|h)|h
  · obtain ⟨hlo,hhi⟩ := h
    interval_cases i <;> simp [restartTargets,List.range_succ,inputs,dataOf]
  · rcases h with rfl|rfl|rfl|rfl
    all_goals simp [restartTargets,inputs]
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [restartTargets,inputs]

theorem restart_literals (B : ℕ) : ∀a∈restartInstructions,a.literalWidth ≤ B+1031 := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  change (inputs zeroData 0 i).bits.length ≤ B+1031
  have hz : zeroData.Width 0 := by
    constructor <;> first | rfl | (intro j;rfl)
  have h := inputs_width zeroData 0 0 0 (by omega) hz i
  norm_num only [inputWidth,pow_zero] at h
  omega

theorem dataOf_width (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length ≤ B) : (dataOf v).Width B := by
  refine ⟨hw 2100 (by decide +kernel),hw 2101 (by decide +kernel),hw 2102 (by decide +kernel),
    hw 2103 (by decide +kernel),hw 2104 (by decide +kernel),hw 2105 (by decide +kernel),
    hw 2106 (by decide +kernel),hw 2107 (by decide +kernel),hw 2108 (by decide +kernel),
    hw 2109 (by decide +kernel),hw 2110 (by decide +kernel),hw 2111 (by decide +kernel),?_⟩
  intro j
  exact hw (2112+j.val) (by simp only [ids,Compare.ids,extra,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton];have := j.isLt;omega)

theorem restart (v : ℕ→ℕ) (e d W B : ℕ) (hC : v 2100=2^e)
    (hm : 0<v 2103) (hKd : 0<v 2105) (hAn : 0<v 2108) (hAd : 0<v 2109)
    (hTn : 0<v 2110) (hTd : 0<v 2111) (hEn : 0<v 2106) (hEd : 0<v 2107)
    (hA : (v 2108:ℚ)/v 2109=alpha (v 2101) d) (hw : ∀i∈ids,(v i).bits.length ≤ W) (hD : (dataOf v).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→RationalAccumulator.Blank s.val i) :
    let D := dataOf v
    let K := (D.conditionNum:ℚ)/D.conditionDen
    let ε := (D.epsilonNum:ℚ)/D.epsilonDen
    let τ := (D.tauNum:ℚ)/D.tauDen
    let hε : 0<ε := div_pos (by exact_mod_cast hEn) (by exact_mod_cast hEd)
    let hτ : 0<τ := div_pos (by exact_mod_cast hTn) (by exact_mod_cast hTd)
    let N := Nat.find (bufferSearch_exists e D.wells D.sourceSize D.length d D.span K ε τ hm hε hτ)
    ∃cost t,Executes input tape restartCode cost s t ∧ cost ≤ resetCost W+costBound N B ∧
      Ready D N (width N B) t ∧ RationalAccumulator.Word t.val 2115
        (selectedBuffer e D.wells D.sourceSize D.length d D.span K ε τ hm hε hτ) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  obtain ⟨rc,u,er,hr,bu,su,fu⟩ := NatAssign.executes ids (fun i hi=>by have := ids_ge i hi;omega)
    restartInstructions restart_valid v input tape s hb (fun i hi=>hs i (by omega))
  have hp := NatAssign.price_bound ids restartInstructions restart_valid v (W+1031)
    (fun i hi=>(hw i hi).trans (by omega)) (restart_literals W)
  have bu' : NatAssign.Bank ids (inputs (dataOf v) 0) u.val := by
    intro i hi
    simpa only [restart_values v i hi] using bu i hi
  have fu' := fu.mono (show NatAssign.changes restartInstructions⊆{0,1,2,3}∪ids by decide +kernel)
  obtain ⟨sc,t,es,hc,ht,hwout,hf⟩ := executes (dataOf v) e d B hC hm hKd hAn hAd hTn hTd hEn hEd hA
    hD input tape u bu' (fifth_scratch fu' hs su)
  exact ⟨rc+sc,t,er.seq es,Nat.add_le_add (hr.trans hp) hc,ht,hwout,(nat_frame fu').trans hf⟩

#print axioms restart
end Maxwell.Continuum.Parameters.BufferMachine
