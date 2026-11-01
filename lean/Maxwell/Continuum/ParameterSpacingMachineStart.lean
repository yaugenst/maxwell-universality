import Maxwell.Continuum.ParameterSpacingMachine

/-! Restart the spacing search using the six actual input words. All search
and comparison work words are reset by the fixed program, so successive outer
stages need no supplied initialization trace. -/

namespace Maxwell.Continuum.Parameters.SpacingMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048
attribute [local irreducible] values width

def dataOf (v : ℕ→ℕ) : Data := ⟨v 2000,v 2001,v 2002,v 2003,v 2004,v 2005⟩
def resetTargets : List ℕ := [30,31,32,33,34,35,36]++(List.range 26).map (2006+·)
def resetInstructions : List NatAssign.Instruction :=
  resetTargets.map fun i => .literal i (inputs ⟨0,0,0,0,0,0⟩ 0 i)
def restartCode : Code := .seq (NatAssign.code resetInstructions) code
def resetCost (B : ℕ) : ℕ := 3000*8^resetInstructions.length*(B+1032)^2

theorem reset_valid : ∀ a∈resetInstructions,a.Valid ids := by
  simp [resetInstructions,resetTargets,List.range_succ,NatAssign.Instruction.Valid,ids,Compare.ids,extra]

theorem reset_values (v : ℕ→ℕ) (i : ℕ) (hi : i∈ids) :
    NatAssign.values resetInstructions v i=inputs (dataOf v) 0 i := by
  rw [resetInstructions,NatAssign.values_literals]
  simp only [ids,Compare.ids,extra,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with h|h
  · obtain ⟨hlo,hhi⟩ := h
    interval_cases i <;> simp [resetTargets,List.range_succ,inputs,dataOf]
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [resetTargets,inputs]

theorem reset_literals (B : ℕ) : ∀ a∈resetInstructions,a.literalWidth≤B+1030 := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  change (inputs ⟨0,0,0,0,0,0⟩ 0 i).bits.length≤B+1030
  simp only [inputs,pow_zero,pow_one]
  split_ifs <;> first
    | (change 0≤B+1030;omega) | (change 1≤B+1030;omega)
    | (change 2≤B+1030;omega) | (change 4≤B+1030;omega)
    | (change 25≤B+1030;omega) | (change 1027≤B+1030;omega)

theorem dataOf_width (v : ℕ→ℕ) (B : ℕ) (hw : ∀ i∈ids,(v i).bits.length≤B) :
    (dataOf v).Width B := by
  exact ⟨hw 2000 (by decide),hw 2001 (by decide),hw 2002 (by decide),
    hw 2003 (by decide),hw 2004 (by decide),hw 2005 (by decide)⟩

theorem restart (v : ℕ→ℕ) (e W B : ℕ) (hC : v 2000=2^e)
    (hKn : 0<v 2002) (hKd : 0<v 2003) (hEn : 0<v 2004) (hEd : 0<v 2005)
    (hw : ∀ i∈ids,(v i).bits.length≤W) (hD : (dataOf v).Width B)
    (input : List Bool) (randomTape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : NatAssign.Scratch s.val) :
    let D := dataOf v
    let K := (D.conditionNum:ℚ)/D.conditionDen
    let ε := (D.epsilonNum:ℚ)/D.epsilonDen
    let hK : 0<K := div_pos (by exact_mod_cast hKn) (by exact_mod_cast hKd)
    let hε : 0<ε := div_pos (by exact_mod_cast hEn) (by exact_mod_cast hEd)
    let N := Nat.find (spacingSearch_exists e D.length K ε hK hε)
    ∃ cost t, Executes input randomTape restartCode cost s t ∧
      cost≤resetCost W+costBound N B ∧ Ready D N (width N B) t ∧
      RationalAccumulator.Word t.val 2006 (selectedSpacing e D.length K ε hK hε) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  obtain ⟨rc,u,er,hr,bu,su,fu⟩ := NatAssign.executes ids ids_ge resetInstructions reset_valid
    v input randomTape s hb hs
  have hp := NatAssign.price_bound ids resetInstructions reset_valid v (W+1030)
    (fun i hi => (hw i hi).trans (by omega)) (reset_literals W)
  have hr' : rc≤resetCost W := by simpa only [resetCost,Nat.add_assoc] using hr.trans hp
  have bu' : NatAssign.Bank ids (inputs (dataOf v) 0) u.val := by
    intro i hi
    simpa only [reset_values v i hi] using bu i hi
  obtain ⟨sc,t,es,hc,ht,hwout,hf⟩ := executes (dataOf v) e B hC hKn hKd hEn hEd
    hD input randomTape u bu' su
  exact ⟨rc+sc,t,er.seq es,Nat.add_le_add hr' hc,ht,hwout,
    (fu.mono (by decide +kernel)).trans hf⟩

#print axioms restart

end Maxwell.Continuum.Parameters.SpacingMachine
