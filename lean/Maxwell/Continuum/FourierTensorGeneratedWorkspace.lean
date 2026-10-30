import Maxwell.Continuum.FourierTensorStart
import Maxwell.Continuum.FourierTensorRowHandoff

/-! The generated row loop returns exactly the workspace consumed by
the tensor startup after its charged header handoff. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536

theorem generated_upper {input : List Bool} {tape : ℕ→Bool} {j : Fin 3}
    {cost : ℕ} {s t : Store} (e : Executes input tape (generatedCode j) cost s t)
    (i : ℕ) (hlo : 1084 ≤ i) (hhi : i<1111) : t.val.tapes i=s.val.tapes i := by
  have syntactic : (generatedCode j).outsideTapes 1084 1111=true := by
    fin_cases j <;> decide
  exact e.outsideTapes syntactic i hlo hhi

theorem generated_power_count {cost : ℕ} (M L R P W : ℕ) (hW : 5≤W)
    (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (hw : InputWidth M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator) W)
    (input : List Bool) (tape : ℕ→Bool) (s t : Store)
    (hb : NatAssign.Bank ids (initial M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val)
    (hz : NatAssign.Scratch s.val) (h144 : Blank s.val 144) (h146 : Blank s.val 146)
    (e : Executes input tape (generatedCode j) cost s t) : Blank t.val 146 := by
  cases e with
  | seq allocated rest =>
    cases allocated with
    | seq setup allocate =>
      obtain ⟨c,u,run,_,bank,_,_,_⟩ := executes M L R P _ _ _ _ W hW hw input tape s hb hz
      have same := setup.deterministic run
      rw [same.2] at allocate
      have word := bank 145 (by simp [ids])
      rw [values_precision] at word
      have word' := RationalAccumulator.word_of_eq (allocate.protectsTape 145 (by decide)) word
      cases rest with
      | seq power rows =>
        have z144 := RationalAccumulator.blank_of_eq
          ((allocate.protectsTape 144 (by decide)).trans (run.protectsTape 144 (by decide))) h144
        have z146 := RationalAccumulator.blank_of_eq
          ((allocate.protectsTape 146 (by decide)).trans (run.protectsTape 146 (by decide))) h146
        obtain ⟨c1,v,e1,_,_,_,blank,_⟩ := DyadicFloor.StoredPower.power_executes P input tape _ word' z146 z144
        have same1 := power.deterministic e1
        rw [same1.2] at rows
        exact RationalAccumulator.blank_of_eq
          (ModePrepare.table_executes_retained rows 146 (by simp [ModePrepare.retainedPorts])) blank

theorem generated_phase {input : List Bool} {tape : ℕ→Bool} {j : Fin 3}
    {cost : ℕ} {s t : Store} {v : ℕ→Parts}
    (e : Executes input tape (generatedCode j) cost s t)
    (hp : Phase.Runtime.Clean s.val) (hr : Ready RowArithmetic.bank v t) : Phase.Runtime.Clean t.val := by
  intro i hi
  by_cases low : i∈RationalMagnitude.ids
  · have him : i∈RationalDataflow.ids RowArithmetic.bank :=
      Finset.mem_union_right _ (Finset.mem_union_right _ low)
    have hlow : i<1000 := by
      simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at low
      omega
    have word := hr.1 i him
    rw [dataValues_small v hlow,RationalAccumulator.zero_word_iff_blank] at word
    exact word
  · have range : 600 ≤ i ∧ i<725 := by
      simp only [Finset.mem_erase,PhaseMachine.Runtime.ids,PhaseMachine.Runtime.extras,
        PhaseMachine.allIds,PhaseMachine.ids,Machin.allIds,RationalTaylor.ids,RationalArctan.ids,
        RationalMagnitude.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi low
      omega
    exact RationalAccumulator.blank_of_eq (generated_middle e i range.1 range.2) (hp i hi)

theorem handoff_phase {s t : Store} (hp : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame RowHandoff.changed s.val t.val) : Phase.Runtime.Clean t.val := by
  intro i hi
  exact RationalAccumulator.blank_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint ((PhaseMachine.Runtime.ids.erase 652).erase 653) RowHandoff.changed) hi)) (hp i hi)

theorem handoff_setup {input : List Bool} {tape : ℕ→Bool} {j : Fin 3}
    {Q N cost : ℕ} {s t u : Store} (e : Executes input tape (generatedCode j) cost s t)
    (h : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (f : BinaryPrecision.Frame RowHandoff.changed t.val u.val)
    (hz : ∀i∈RowHandoff.cleared,Blank u.val i) : NatAssign.Bank setupIds (initialSetup Q N) u.val := by
  intro i hi
  by_cases hc : i=145 ∨ i=201
  · have hic : i∈RowHandoff.cleared := by simp only [RowHandoff.cleared,List.mem_cons,List.not_mem_nil,or_false];omega
    simpa [initialSetup,initialDimensions,show i≠710 by omega,show i≠711 by omega,
      RationalAccumulator.zero_word_iff_blank] using hz i hic
  · have range : 600 ≤ i ∧ i<725 := by
      simp only [setupIds,dimensionIds,parameterIds,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have ho : i∉RowHandoff.changed := by
      simp only [RowHandoff.changed,RowHandoff.cleared,headerSlots,List.mem_toFinset,
        List.mem_cons,List.not_mem_nil,or_false,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact RationalAccumulator.word_of_eq ((f.tapes i ho).trans (generated_middle e i range.1 range.2)) (h i hi)

theorem handoff_fresh {input : List Bool} {tape : ℕ→Bool} {j : Fin 3}
    {cost : ℕ} {s t u : Store} (e : Executes input tape (generatedCode j) cost s t)
    (h : ∀i∈TensorStart.freshPorts,Blank s.val i) (h146 : Blank t.val 146)
    (f : BinaryPrecision.Frame RowHandoff.changed t.val u.val)
    (hz : ∀i∈RowHandoff.cleared,Blank u.val i) (h216 : Blank u.val 216) :
    ∀i∈TensorStart.freshPorts,Blank u.val i := by
  intro i hi
  by_cases hc : i∈RowHandoff.cleared
  · exact hz i hc
  by_cases h216' : i=216
  · simpa only [h216'] using h216
  by_cases h146' : i=146
  · subst i
    exact RationalAccumulator.blank_of_eq (f.tapes 146 (by decide)) h146
  have ranges : (600 ≤ i ∧ i<725) ∨ (1084 ≤ i ∧ i<1111) := by
    simp only [TensorStart.freshPorts,TensorRegisters.ports,Profile.Runtime.CacheAllocation.inputs,savedPorts,StoredParts.ports,
      RowHandoff.cleared,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton,
      List.mem_cons,List.not_mem_nil,or_false] at hi hc
    omega
  have keep : u.val.tapes i=t.val.tapes i := f.tapes i (by
    simp only [RowHandoff.changed,RowHandoff.cleared,headerSlots,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil,or_false,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega)
  apply RationalAccumulator.blank_of_eq (keep.trans _) (h i hi)
  rcases ranges with hm|hu
  · exact generated_middle e i hm.1 hm.2
  · exact generated_upper e i hu.1 hu.2

#print axioms handoff_fresh
#print axioms handoff_setup
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
